/-
LeanAction.Derive
=================

Command-style generation of `View`s and `Lens`es for structure fields.

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

private def elabViewLike (lens : Bool) (ty : Term) : CommandElabM Unit := do
  let some tyStr := Syntax.reprint ty.raw
    | throwError "view_defs: cannot read the type expression back as a string"
  let tyName ← liftTermElabM do
    let e ← Term.elabType ty
    match e.consumeMData.getAppFn with
    | .const n _ => pure n
    | _ => throwError "view_defs: expected a structure (a constant type)"
  let env ← getEnv
  let some info := getStructureInfo? env tyName
    | throwError "view_defs: `{tyName}` is not a structure"
  -- declaration names must be *relative* to the current namespace: `elabCommand`
  -- prefixes it, so an absolute name would be doubled
  let currNs ← getCurrNamespace
  let relTy :=
    if currNs == .anonymous then tyName
    else
      let rel := tyName.replacePrefix currNs .anonymous
      if rel == tyName && !currNs.isPrefixOf tyName then
        rel
      else rel
  unless currNs == .anonymous || currNs.isPrefixOf tyName do
    throwError "view_defs: `{tyName}` is outside the current namespace `{currNs}`; \
      generated names would land in the wrong place"
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
        `(def $declId := Lens.mk $getter $setter
            (by intro s a; rfl) (by intro s; cases s; rfl) (by intro s a b; cases s; rfl))
      else
        `(def $declId := View.mk $getter $setter)
    elabCommand cmd

/-- `view_defs Struct` generates a proof-free `View` (`Struct.fView`) for every
field of the structure. -/
elab "view_defs" ty:term : command => elabViewLike false ty

/-- `lens_defs Struct` generates a `Lens` (`Struct.fLens`) for every field of the
structure, discharging the three lens laws by structure eta (`rfl`). -/
elab "lens_defs" ty:term : command => elabViewLike true ty

end LeanAction
