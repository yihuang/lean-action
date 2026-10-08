/-
LeanAction.Derive
=================

Generation of `View`s and `Lens`es for structure fields, in two flavours:

* **`deriving ViewFields, LensFields`** on a structure: the ergonomic path. It
  emits `Struct.fView`/`Struct.fLens` for every field, with absolute declaration
  names (so it works inside namespaces) and no restrictions on doc comments.
* **`view_defs T` / `lens_defs T`** commands: the general path, which takes the
  type as a *term* so parameterized structures work
  (`view_defs (Box α)` inside a `section` with `variable (α : Type)`).

The deriving handler declines parameterized structures with a clear message: the
framework names the parameter binders hygienically, so they cannot be written
into the getter/setter strings. The commands avoid that by having the *user*
spell the type out.

**Why a command and not a term macro.** The field position in `{ s with f := v }`
is a `Lean.Parser.Term.structInstLVal` syntax node. A term macro cannot produce
one from an `ident` antiquotation: the expansion is rejected at the *use site*
(`unexpected syntax`) while the macro definition itself elaborates happily — a
misleading failure that cost two attempts. Here the getter and the setter are
*parsed* from a string, which yields well-formed nodes, and the declaration is
then elaborated with `elabCommand`.

Generated names are namespaced under the structure: `view_defs Ctr` produces
`Ctr.nView`, `Ctr.logView`, … and `lens_defs Ctr` produces `Ctr.nLens`, ….

Two gotchas, both found the hard way:

* a custom command cannot be preceded by a **doc comment** (`/-- … -/`): doc
  comments are only attached to declaration commands, so the parser rejects
  `/-- … -/ view_defs Foo`. Use a regular `/- … -/` comment instead;
* the structure must live in the current namespace (or a sub-namespace), because
  `elabCommand` prefixes declaration names with the current namespace — an
  absolute name would land in `<ns>.<ns>.<Struct>.<field>View`. The command
  errors out clearly if that would happen.
-/
import Lean
import LeanAction.Lens

open Lean Elab Command

namespace LeanAction

/-- The leftmost identifier of a syntax tree, if any. Used to read the structure
name out of the type expression *syntactically*: elaborating the type would need
the section variables, which a custom command's `liftTermElabM` does not see (the
generated definitions do see them, since they are elaborated as declarations). -/
private partial def headIdentName? : Syntax → Option Name
  | .ident _ _ n _ => if n == .anonymous then none else some n
  | .node _ _ args => args.findSome? headIdentName?
  | _ => none

/-- Resolve the structure name from a type expression, trying the name as written,
under the current namespace, and after stripping `_root_.`. -/
private def structName? (env : Environment) (currNs : Name) (stx : Syntax) : Option Name :=
  let n := headIdentName? stx
  let cands :=
    match n with
    | some n => #[n, currNs ++ n, n.replacePrefix `_root_ .anonymous]
    | none => #[]
  cands.find? fun c => (getStructureInfo? env c).isSome

/-- Flatten a syntactic application `f a b …` into its head and the argument
list, stripping parentheses. Returns `(stx, #[])` for a non-application. -/
private partial def flatApp (stx : Syntax) : Syntax × Array Syntax :=
  match stx with
  | .node _ `Lean.Parser.Term.paren args =>
      match args[1]? with
      | some inner => flatApp inner
      | none => (stx, #[])
  | .node _ `Lean.Parser.Term.app args =>
      match args[0]?, args[1]? with
      | some fn, some argSeq =>
          let (head, prev) := flatApp fn
          (head, prev ++ argSeq.getArgs)
      | _, _ => (stx, #[])
  | _ => (stx, #[])

/-- Number of leading *explicit* `forall` binders of a type. A generated view is
a plain `View` unless the structure's parameters were declared with an explicit
`variable` `(α : Type)`, in which case the view is a function and has to be
applied to the type arguments. -/
private def explicitArity : Expr → Nat
  | .forallE _ _ body .default => 1 + explicitArity body
  | _ => 0

/-- The last component of a (possibly namespaced) field name. -/
private def lastComp (n : Name) : String :=
  match n with
  | .str _ s => s
  | _ => n.toString

/-- Parse `fun s : Ty => s.fld` and `fun s v => { s with fld := v }`. -/
private def viewParts (env : Environment) (tyStr fld : String) : Except String (Syntax × Syntax) := do
  let getter ← Parser.runParserCategory env `term s!"fun s : {tyStr} => s.{fld}"
  let setter ← Parser.runParserCategory env `term s!"fun s v => \{ s with {fld} := v }"
  return (getter, setter)

/-- Shared implementation: `tyStr` is the structure type as it should be written
inside the generated definitions (e.g. `Foo` or `Box α`), `binders` are the
parameter binders to put on the generated definition (empty for a structure
without parameters). `relTy` is the declaration name relative to the current
namespace, since `elabCommand` prefixes declaration names with it. -/
private def emitViewLikes (lens : Bool) (tyName : Name) (tyStr : String)
    (binders : Array (TSyntax `Lean.Parser.Term.bracketedBinder)) : CommandElabM Unit := do
  let env ← getEnv
  let some info := getStructureInfo? env tyName
    | throwError "view_defs: `{tyName}` is not a structure"
  let currNs ← getCurrNamespace
  let relTy :=
    if currNs == .anonymous then tyName else tyName.replacePrefix currNs .anonymous
  -- The structure type as a *term*, used to ascribe the view references in the
  -- certificate statements below. Without the ascription a reference like
  -- `Box.payloadView` leaves the structure parameter as an unsolved implicit
  -- (the theorem header is elaborated with no expected type), so the parameter
  -- never enters the section-variable collection and the generated theorem is
  -- ill-formed (`don't know how to synthesize implicit argument α`). Writing
  -- `(Box.payloadView : View (Box α) _)` ties the parameter to the section
  -- variable, which both infers the arguments and pulls `α` into the binders.
  let tyTerm ← match Parser.runParserCategory env `term tyStr with
    | .ok s => pure (⟨s⟩ : TSyntax `term)
    | .error e => throwError "view_defs: cannot parse the type `{tyStr}` back as a term: {e}"
  for fldName in info.fieldNames do
    let fld := lastComp fldName
    let (getterStx, setterStx) ← match viewParts env tyStr fld with
      | .ok p => pure p
      | .error e => throwError "view_defs: {e}"
    let getter : TSyntax `term := ⟨getterStx⟩
    let setter : TSyntax `term := ⟨setterStx⟩
    let declId := mkIdent (relTy.str (fld ++ (if lens then "Lens" else "View")))
    let cmd ←
      if lens then
        `(def $declId $binders* := Lens.mk $getter $setter
            (by intro s a; rfl) (by intro s; cases s; rfl) (by intro s a b; cases s; rfl))
      else
        `(def $declId $binders* := View.mk $getter $setter)
    elabCommand cmd
  -- Certificate layer: one theorem per pair of distinct fields, e.g.
  -- `T.disjoint_f_g : Disjoint T.fView T.gView`, closed by `cases s; rfl`
  -- (deliberately *not* casing the values, which would split `Nat` into
  -- `zero`/`succ` and get stuck). Sibling fields are syntactically disjoint,
  -- so the disjointness check is done here, at generation time; the
  -- `disjoint_auto` tactic only has to look the certificate up *by name*.
  -- Idempotent across the `ViewFields`/`LensFields` pair of handlers via the
  -- contains-check. NB: identifiers are built with `mkIdent` (scope-free) and
  -- antiquoted; literals written inside the quotation get stamped with this
  -- module's macro scopes and fail to resolve at the use site.
  let env ← getEnv
  if env.contains `LeanAction.Disjoint then
    let fields := info.fieldNames
    for i in [:fields.size] do
      for j in [i+1:fields.size] do
        let f := lastComp fields[i]!
        let g := lastComp fields[j]!
        let lemName := relTy.str s!"disjoint_{f}_{g}"
        let env ← getEnv
        if env.contains (currNs ++ lemName) then continue
        let mkViewRef (fld : String) : CommandElabM (TSyntax `term) := do
          let vName := relTy.str (fld ++ "View")
          if (← getEnv).contains (currNs ++ vName) then
            let vId := mkIdent vName
            -- The generated view takes the structure's parameters as *explicit*
            -- arguments when the user declared them with `variable (α : Type)`;
            -- then the bare name is a function and has to be applied. Otherwise
            -- the ascription alone pins the parameters and pulls them into the
            -- theorem's binders.
            let arity : Nat :=
              match (← getEnv).find? (currNs ++ vName) with
              | some ci => explicitArity ci.type
              | none => 0
            if arity == 0 then
              `(($vId : $(mkIdent `LeanAction.View) $tyTerm _))
            else
              let (_, allArgs) := flatApp tyTerm.raw
              if allArgs.size < arity then
                throwError "view_defs: cannot reconstruct the type arguments of \
                  `{tyName}` for the disjointness certificate; spell the full \
                  application out (e.g. `view_defs (Foo α β)`)"
              let args : Array (TSyntax `term) := (allArgs.extract 0 arity).map (⟨·⟩)
              `(($vId $args* : $(mkIdent `LeanAction.View) $tyTerm _))
          else
            -- A `LensFields`-only structure has no `T.fView`; the certificate
            -- uses `View.ofLens T.fLens`. Same arity handling as the view
            -- branch: with `variable (γ : Type)` the lens takes `γ` explicitly,
            -- so the bare name is a function and has to be applied.
            let vName := relTy.str (fld ++ "Lens")
            let vId := mkIdent vName
            let arity : Nat :=
              match (← getEnv).find? (currNs ++ vName) with
              | some ci => explicitArity ci.type
              | none => 0
            if arity == 0 then
              `(($(mkIdent `LeanAction.View.ofLens) $vId : $(mkIdent `LeanAction.View) $tyTerm _))
            else
              let (_, allArgs) := flatApp tyTerm.raw
              if allArgs.size < arity then
                throwError "view_defs: cannot reconstruct the type arguments of \
                  `{tyName}` for the disjointness certificate; spell the full \
                  application out (e.g. `view_defs (Foo α β)`)"
              let args : Array (TSyntax `term) := (allArgs.extract 0 arity).map (⟨·⟩)
              `(($(mkIdent `LeanAction.View.ofLens) ($vId $args*)
                  : $(mkIdent `LeanAction.View) $tyTerm _))
        let fv ← mkViewRef f
        let gv ← mkViewRef g
        let cmd ← `(theorem $(mkIdent lemName) $binders* :
            $(mkIdent `LeanAction.Disjoint) $fv $gv :=
          ⟨by intro s a; cases s; rfl,
             by intro s b; cases s; rfl,
             by intro s a b; cases s; rfl⟩)
        elabCommand cmd

private def elabViewLike (lens : Bool) (ty : Term) : CommandElabM Unit := do
  let some tyStr := Syntax.reprint ty.raw
    | throwError "view_defs: cannot read the type expression back as a string"
  let env ← getEnv
  let currNs ← getCurrNamespace
  let some tyName := structName? env currNs ty.raw
    | throwError "view_defs: `{tyStr}` does not name a structure"
  unless currNs == .anonymous || currNs.isPrefixOf tyName do
    throwError "view_defs: `{tyName}` is outside the current namespace `{currNs}`; \
      generated names would land in the wrong place"
  emitViewLikes lens tyName tyStr #[]

/-- Deriving-handler implementation: same generation, but the type string is
taken from the structure's own parameter binders, so parameterized structures
work too, and declaration names are absolute. -/
private def deriveViewLikes (lens : Bool) (declNames : Array Name) : CommandElabM Bool := do
  let some tyName := declNames[0]? | return false
  if declNames.size != 1 then return false
  let env ← getEnv
  let some ci := env.find? tyName | return false
  let .inductInfo indVal := ci | return false
  let some _ := getStructureInfo? env tyName | return false
  -- `mkHeader` names the parameter binders hygienically, so they cannot be
  -- written into the getter/setter strings; for now parameterized structures go
  -- through the commands, where the type is written out as a term.
  if indVal.numParams != 0 then
    throwError "deriving ViewFields/LensFields: `{tyName}` has {indVal.numParams} \
      parameter(s). Use the commands instead, e.g.\n  view_defs ({tyName} α)\n  \
      lens_defs ({tyName} α)"
  emitViewLikes lens tyName (toString tyName) #[]
  return true

/-- Marker class for `deriving ViewFields`: no instances are created, the
deriving handler instead emits one `View` per field (`Struct.fView`). The class
has to exist for the name in the `deriving` clause to resolve. -/
class ViewFields (σ : Type u)

/-- Marker class for `deriving LensFields`: emits one `Lens` per field
(`Struct.fLens`), with the lens laws closed by structure eta. -/
class LensFields (σ : Type u)

initialize
  Lean.Elab.registerDerivingHandler `LeanAction.ViewFields (deriveViewLikes false)
  Lean.Elab.registerDerivingHandler `LeanAction.LensFields (deriveViewLikes true)

/-- `view_defs Struct` generates a proof-free `View` (`Struct.fView`) for every
field of the structure. -/
elab "view_defs" ty:term : command => elabViewLike false ty

/-- `lens_defs Struct` generates a `Lens` (`Struct.fLens`) for every field of the
structure, discharging the three lens laws by structure eta (`rfl`). -/
elab "lens_defs" ty:term : command => elabViewLike true ty

end LeanAction
