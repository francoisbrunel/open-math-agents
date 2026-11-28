module
public meta import Lean

/-! Read a large witness as 1024-bit chunks. The elaborator emits one
ordinary natural literal. The kernel still checks every certificate. -/
public meta section
open Lean Elab Term

elab "weight687%" "[" ns:num,* "]" : term => do
  let mut value := 0
  for n in ns.getElems do
    let some digit := n.raw.isNatLit? | throwError "expected a natural numeral"
    if digit ≥ 2^1024 then throwError "weight chunk exceeds 1024 bits"
    value := value <<< 1024 ||| digit
  return mkNatLit value
