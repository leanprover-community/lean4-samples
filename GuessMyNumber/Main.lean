import Std.Data

-- Generate a "random" number in [0, 99]
-- It's not actually random. We'll talk about it later.
def GetSecret : IO Nat :=
  IO.rand 0 99

partial def guess (secret : Nat) (prompt : String) : IO Unit := do
  IO.println prompt
  let stdin := (←IO.getStdin)
  let str   := (←stdin.getLine)

  if str.length == 0 then -- handles eof.
    return

  let num   := str.trim.toNat?
  match num with
  | none   => guess secret "Please enter a valid number"
  | some i =>
    match (Ord.compare i secret) with
    | Ordering.eq => IO.println "It's correct!"
    | Ordering.lt => guess secret "Too small"
    | Ordering.gt => guess secret "Too large"

partial def main : IO Unit := do
  let secret := (←GetSecret)
  guess secret "Please enter a number"
