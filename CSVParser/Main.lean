import CSVParser

/-!
  ## The data
-/

def csvString : String := "a,\"b\nc\"\r\n1,2"

#eval parse csvString

/-!
  ## Challenge: Homogenous
-/

def csvString' : String := "a,\"b\nc\"\r\n1,2\r\n4,5,6"

#eval parse csvString'

/-
Notice that in Lean the order of a source file matters.  This following #eval looks the same as before
but it will pick up the new code we just wrote and behave differently. -/
#eval parse' csvString'


def main : IO Unit :=
  let csv := parse csvString
  match csv with
  | .ok r => IO.println s!"parsed {r.size} rows of data"
  | .error e => IO.println s!"invalid csv data: {e}"
