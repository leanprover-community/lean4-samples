import Std.Data

-- Generate a "random" number in [0, 99]
-- It's not actually random. We'll talk about it later.
def getSecret : IO Nat := do
  let seed ← (UInt64.toNat ∘ ByteArray.toUInt64LE!) <$> IO.getRandomBytes 8
  IO.setRandSeed seed
  IO.rand 0 99

partial def guess (secret : Nat) (prompt : String) : IO Unit := do
  IO.println prompt
  let stdin := (←IO.getStdin)
  let mut str ← stdin.getLine
  str := str.trim

  if str.length == 0 then
    IO.println s!"Giving up? Well the number was {secret}"
    return

  match str.toNat? with
  | .none   => guess secret "Please enter a valid number"
  | .some i =>
    match Ord.compare i secret with
    | .eq => IO.println s!"It's correct! The number was {secret}!"
    | .lt => guess secret "Too small, try again?"
    | .gt => guess secret "Too large, try again?"

def main : IO Unit := do
  IO.println "I am thinking of a number between 0 and 99..."
  let secret ← getSecret
  guess secret "Please guess what it is?"
