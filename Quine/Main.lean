def s := "\ndef main : IO Unit := do\n  IO.println (\"def s := \" ++ s.quote)\n  IO.println (s)"

def main : IO Unit := do
  IO.println ("def s := " ++ s.quote)
  IO.println (s)
