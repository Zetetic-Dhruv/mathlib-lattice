import Lean
import MathlibLattice

/-! Prints one JSON line per declaration of the project: name, module, kind, source line, the
line of its name, whether it was written in the source or generated, whether its statement or
its own proof uses `sorry`, the project constants its statement mentions, the project constants
its proof or body mentions, the number of Mathlib constants it mentions, and its docstring. -/

open Lean

private def projModule (env : Environment) (n : Name) : Option Name :=
  match env.getModuleIdxFor? n with
  | some idx =>
    let m := env.header.moduleNames[idx.toNat]!
    if (`MathlibLattice).isPrefixOf m then some m else none
  | none => none

private def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .axiomInfo _ => "axiom"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"

/-- Equation lemmas `f.eq_1`, `f.eq_2`, ... and `f.eq_def`. -/
private def isEqnName : Name → Bool
  | .str _ s => s == "eq_def" || s == "eq_unfold" ||
      (s.startsWith "eq_" && s.length > 3 && (s.drop 3).all Char.isDigit)
  | _ => false

private def skip (env : Environment) (n : Name) (ci : ConstantInfo) : Bool :=
  n.isInternalDetail || isAuxRecursor env n || isNoConfusion env n || isEqnName n ||
    (match ci with | .recInfo _ => true | _ => false)

#eval show CoreM Unit from do
  let env ← getEnv
  for (n, ci) in env.constants.map₁.toList do
    let some m := projModule env n | continue
    if skip env n ci then continue
    let ty := ci.type.getUsedConstants
    let val := ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
    let proj := fun (xs : Array Name) =>
      (xs.filter (fun c => (projModule env c).isSome && c != n)).toList.eraseDups
    let mathlib := ((ty ++ val).filter (fun c => (projModule env c).isNone)).toList.eraseDups.length
    let doc := (← findDocString? env n).getD ""
    let ranges ← findDeclarationRanges? n
    let line : Nat := (ranges.map (·.range.pos.line)).getD 0
    let selLine : Nat := (ranges.map (·.selectionRange.pos.line)).getD 0
    let j := Json.mkObj [
      ("name", toJson n.toString), ("module", toJson m.toString), ("kind", toJson (kindOf ci)),
      ("line", toJson line), ("sel_line", toJson selLine), ("generated", toJson ranges.isNone),
      ("sorry_stmt", toJson (ty.contains ``sorryAx)),
      ("sorry", toJson (val.contains ``sorryAx || ty.contains ``sorryAx)),
      ("stmt_deps", toJson ((proj ty).map toString)),
      ("proof_deps", toJson ((proj val).map toString)),
      ("mathlib_refs", toJson mathlib), ("doc", toJson doc)]
    IO.println j.compress
