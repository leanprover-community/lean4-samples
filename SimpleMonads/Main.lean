import Monads

def main (args: List String): IO Unit := do
  let ret := divideRefactored 5 0 args 10
  let msg := match ret with
  | .ok s => toString s
  | .error e => e
  IO.println s!"{msg}"

#eval main []           -- can't divide by zero
#eval main ["--limit"]  -- too many divides
