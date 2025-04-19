import BiasedBisect
import Batteries.Data.Rat.Float

def stringToPNat (str: String): Option ℕ+ :=
  do
  let i ← str.toInt?
  let n ← i.toNat?
  if h: 0 < n then
    some <| n.toPNat h
  else
    none

def main (args : List String) : IO Unit := do
  match args with
  | [s, t, n] =>
    let s ← match stringToPNat s with
    | none =>
      throw (IO.userError "s is not a valid positive integer")
    | some x => pure x
    let t ← match stringToPNat t with
    | none =>
      throw (IO.userError "t is not a valid positive integer")
    | some x => pure x
    let n ← match stringToPNat n with
    | none =>
      throw (IO.userError "n is not a valid positive integer")
    | some x => pure x
    let list := calculateBbList s t n
    for entry in list do
      IO.println s!"n = {entry.n}, E = {entry.En}, wₘᵢₙ = {entry.wₘᵢₙn}, wₘₐₓ = {entry.wₘₐₓn}, wₗᵢ = {entry.wₗᵢn.toFloat}"
  | _ => throw (IO.userError "Bad input format")
