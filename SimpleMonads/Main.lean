import Monads

def main (s: List String): IO Unit := do
  IO.println (match (divideRefactored 5 2 s 10) with
  | Except.error s => s
  | Except.ok r => toString r)
