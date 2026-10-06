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
