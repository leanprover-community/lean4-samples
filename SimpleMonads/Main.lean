import Monads

def liftIO (t : Except String α ) : IO α :=
  match t with
  | .ok r => EStateM.Result.ok r
  | .error s => EStateM.Result.error s

def main (args: List String): IO Unit := do
  try
    let ret ← liftIO (divideRefactored 5 0 args 10)
    IO.println (toString ret)
  catch e =>
    IO.println e

#eval main []           -- can't divide by zero
#eval main ["--limit"]  -- too many divides
