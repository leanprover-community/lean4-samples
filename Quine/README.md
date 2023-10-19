## Quine example

This is an example of a program that outputs its own source code.

```bash
~/lean4-samples/Quine$ lake build && build/bin/quine
def s := "\ndef main : IO Unit := do\n  IO.println (\"def s := \" ++ s.quote)\n  IO.println (s)"

def main : IO Unit := do
  IO.println ("def s := " ++ s.quote)
  IO.println (s)
~/lean4-samples/Quine$ cat Main.lean
def s := "\ndef main : IO Unit := do\n  IO.println (\"def s := \" ++ s.quote)\n  IO.println (s)"

def main : IO Unit := do
  IO.println ("def s := " ++ s.quote)
  IO.println (s)
```

This relies on the `quote` method of `String.quote : String → String`, which escapes and quotes a string.
