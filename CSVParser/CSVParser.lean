import Lean.Data.Parsec

open Lean Parsec

/-!
  ## The strucutre of CSV
-/

abbrev Field := String
abbrev Record := Array Field
abbrev Csv := Array Record

/-!
  ## The parser
-/

def textData : Parsec Char := satisfy fun c =>
  0x20 ≤ c.val ∧ c.val ≤ 0x21 ∨
  0x23 ≤ c.val ∧ c.val ≤ 0x2B ∨
  0x2D ≤ c.val ∧ c.val ≤ 0x7E

def cr : Parsec Char := pchar '\r'
def lf : Parsec Char := pchar '\n'
def crlf : Parsec String := pstring "\r\n"
def comma : Parsec Char := pchar ','
def dQUOTE : Parsec Char := pchar '\"'
def twoDQUOTE  : Parsec Char :=  attempt (pchar '"' *> pchar '"')

def escaped : Parsec String := attempt
  dQUOTE *>
  manyChars (textData <|> comma <|> cr <|> lf <|> twoDQUOTE)
  <* dQUOTE

def nonEscaped: Parsec String := manyChars textData

def field : Parsec Field := escaped <|> nonEscaped

/--
  Many `p` separated by `s`.
-/
def manySep (p : Parsec α) (s : Parsec β) : Parsec $ Array α := do
  manyCore (attempt (s *> p)) #[←p]

def record : Parsec Record := manySep field comma

def file : Parsec $ Array Record :=
  manySep record (crlf <* notFollowedBy eof) <* (optional crlf) <* eof

def parse (s : String) : Except String $ Array $ Array $ String :=
  match file s.mkIterator with
  | Parsec.ParseResult.success _ res => Except.ok res
  | Parsec.ParseResult.error it err  => Except.error s!"offset {it.i.byteIdx}: {err}"


-- **Homogeneous CSV parser:**

/--
  Many arrays of `p` with the same size.
-/
partial def manyHomoCore (p : Parsec $ Array α) (acc : Array $ Array α) : Parsec $ Array $ Array α :=
  (do
    let first ← p
    -- if accumulator is empty (the first element) we won't check size
    if acc.size = 0 then
      manyHomoCore p (acc.push first)     -- recursively
    else
      -- check whether the new arr is of the same size
      if acc.back.size = first.size then
        manyHomoCore p (acc.push first)   -- recursively
      else
        fail "expect same size"
  )
  -- if not homo, fail and return the accumulator
  <|> pure acc

/--
  Many arrays of `p` with the same size separated by `s`.
-/
def manySepHomo (p : Parsec $ Array α) (s : Parsec β) : Parsec $  Array $ Array α := do
  manyHomoCore (attempt (s *> p)) #[←p]

def file' : Parsec $ Array Record := manySepHomo record (crlf <* notFollowedBy eof) <* (optional crlf) <* eof

def parse' (s : String) : Except String $ Array $ Array $ String :=
  match file' s.mkIterator with
  | Parsec.ParseResult.success _ res => Except.ok res
  | Parsec.ParseResult.error it err  => Except.error s!"offset {it.i.byteIdx}: {err}"
