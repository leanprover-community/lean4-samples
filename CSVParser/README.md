## CSV Parser Sample

The CSV parser may be the simplest but practial parser in the world. In this sample, we will try to write one with the Lean programming language.

For simplicity, we will stick to the [RFC 4180](https://datatracker.ietf.org/doc/html/rfc4180) format, without any extenions, which has the ABNF grammer of:

```abnf
file        = [header CRLF] record *(CRLF record) [CRLF]
header      = name *(COMMA name)
record      = field *(COMMA field)
name        = field
field       = (escaped / non-escaped)
escaped     = DQUOTE *(TEXTDATA / COMMA / CR / LF / 2DQUOTE) DQUOTE
non-escaped = *TEXTDATA
COMMA       = %x2C
CR          = %x0D 
DQUOTE      = %x22
LF          = %x0A 
CRLF        = CR LF 
TEXTDATA    = %x20-21 / %x23-2B / %x2D-7E
```

And we will use this hand crafted CSV string:

```lean
def csvString : String := "a,\"b\nc\"\r\n1,2"
-- which is (without escape) actually
-- a,"b\nc"\r\n1,2
-- and should be parsed into
-- [["a", "b\nc"], ["1", "2"]]
```

## Parser in Functional Programming

When it comes to parsing in functional programming, people often adopt a pattern called "parser combinator". The idea is first invented in Haskell, and today even many imperative languages has implemented it, e.g. [nom](https://github.com/Geal/nom) for Rust and [scala-parser-combinators](https://github.com/scala/scala-parser-combinators) for Scala.

Lean also has a parser combinator implemented in it core, called `Parsec` (The Lean one is named after that in Haskell, but they are of a bit difference. We will talk about that later).

The `Parsec` is defined in `Lean.Data.Parsec`. For using it you should add the following lines on top of your file:

```lean
import Lean.Data.Parsec

open Lean Parsec
```

## Data Structure to Keep the Parsing Result

Before writing the parsing code, it's helpful to forget about the syntax and think about what the parsed data should look like.

We all knows that CSV file carries a sequence of records, and each record consists of several fields. (CSV may also have an optional header, but it's okay to treat them same as record). Also each line should have the same number of fields, but temporarily just ignore it and we will talk about that later. 

So our definition for CSV may look like this:

```lean
abbrev Field := String
abbrev Record := Array Field
abbrev Csv := Array Record
```

## Let's Start Parsing

Different from that in imperative parser, in functional parser combinator you first have small parsers and then combine them into bigger ones. The overview structure of our parsers is of the same structure of ABNF:

![Parsers Overview](./ParsersOverview.drawio.svg)

As we said we will ignore the header path and focus on record only.

### The Basic Parsers

At the bottom of the diagram are the basic parsers. We may implement one by one.

The `DQUOTE` double quote can be defined as:

```lean
def dQuote : Parsec Char := pchar '"'
```

The `pchar` can be thought of as the abbreviation of "parser char". It takes a `Char` and try to match that `Char` in the `String`. 

In the same logic, `COMMA`, `LF`, `CR` can be represented as:

```lean
def comma : Parsec Char := pchar ','
def cr : Parsec Char := pchar '\r'
def lf : Parsec Char := pchar '\n'
```

`TEXTDATA` is a bit more complex. Instead of `pchar` we use `satisfy` which takes a function of `Char -> Bool`, so we can parse any `Char`s that satisfy the given function.

```lean
def textData : Parsec Char := satisfy fun c =>
  0x20 ≤ c.val ∧ c.val ≤ 0x21 ∨
  0x23 ≤ c.val ∧ c.val ≤ 0x2B ∨ 
  0x2D ≤ c.val ∧ c.val ≤ 0x7E
```

### The Combinator

After creating the "bottom" parsers, we can combine them into larger ones.

The most simplest one is `2DQUOTE`:

```lean
def twoDQuote : Parsec Char := attempt (pchar '"' *> pchar '"')
```

The `*>` operator is used to sequence two parsers. The first parser's result is ignored, and the sequenced parsers return the second result.

The `attempt` is used because we want the two `Parsec` to match as a whole. The string iterator will be reset to before `attempt` if any parser in the bracket fails (e.g. The first `pchar`).

Then the `escaped`:

```lean
def escaped : Parsec String := 
  DQUOTE *>
  manyChars (TEXTDATA <|> COMMA <|> CR <|> LF <|> «2DQUOTE»)
  <* DQUOTE
```

The `<*` operator is similar to `*>` but the left is kept and while right one is ignored.

The `<|>` operator is used for alternatives. Once the first parsec fails, it will try the second one, then the third, ...

`non-escaped`:

```lean
def nonEscaped : Parsec String := manyChars textData
```

`manyChars` takes a `Parsec Char` and matches zero or more that parser and merge them into a `String`.

```lean
def field : Parsec Field := escaped <|> nonEscaped
```

There are so many combinators in the Lean core, and you can look at them in the [documentation](https://leanprover-community.github.io/mathlib4_docs/Lean/Data/Parsec.html#Lean.Parsec.pchar).

### A More Complex Parsec

The `record` in CSV is defined as:

```
record = field *(COMMA field)
```

So a `record` consists of `field`s separated by `comma`.

Natually, we want to write the parser like this:

```lean
def record : Parsec Record := manySep field comma
```

But actually there not a `manySep` function provided by Lean, and we need to write it ourselves. Fortunately there is a similar one we have used, the `manyChars`.

There are several `many*` combinators in `Parsec`:

```lean
@[inline]
partial def manyCharsCore (p : Parsec Char) (acc : String) : Parsec String :=
  (do manyCharsCore p (acc.push $ ←p))
  <|> pure acc

@[inline]
def manyChars (p : Parsec Char) : Parsec String := manyCharsCore p ""

@[inline]
def many1Chars (p : Parsec Char) : Parsec String := do manyCharsCore p (←p).toString

@[inline]
partial def manyCore (p : Parsec α) (acc : Array α) : Parsec $ Array α :=
  (do manyCore p (acc.push $ ←p))
  <|> pure acc

@[inline]
def many (p : Parsec α) : Parsec $ Array α := manyCore p #[]

@[inline]
def many1 (p : Parsec α) : Parsec $ Array α := do manyCore p #[←p]
```

Looking at how `manyChars` is implemented. It invokes a recursive function `manyCharsCore` and gives an intial accumulator `String` of `""` Then the `manyCharsCore` iteratively matches the `p` parsec and return the accumulator when it fail. The `many` combinator also works in the same way.

So we can follows this pattern and write our own:

```lean
def manySep (p : Parsec α) (s : Parsec β) : Parsec $ Array α := do
  manyCore (attempt (s *> p)) #[←p]
```

The `manySep` is very similar to that of `many1`, except that requires a prefix separator `s` before each `p` match except for the first one.

The `file` works similarly to `record` except that we use `crlf` as separator. 

```lean
def file : Parsec $ Array Record := manySep record (crlf <* notFollowedBy eof) <* (optional crlf) <* eof
```

The `notFollowedBy`, `optional` and `eof` is used to handle the optional new line at the end of the CSV file.

### Parse it!

Everything is done now. Let's parse a CSV file. We can now use the parser we wrote to parse the `csvString`. A `Parsec` takes a `String.Iterator` and returns the `ParseResult`.

```lean
#eval file csvString.mkIterator
```

If you are in VSCode you can move your cursor onto the `#eval` and you can see the result.

![](./screenshot.png)

The `ParseResult` return value is not very easy to cope with, so we can use a wrapper to lift it into an `Except`.

```lean
def parse (s : String) : Except String $ Array $ Array $ String :=
  match file s.mkIterator with
  | Parsec.ParseResult.success _ res => Except.ok res
  | Parsec.ParseResult.error it err  => Except.error s!"offset {it.i.repr}: {err}"

#eval parse csvString
```

## Some Extra Tricks

### Code Structure

To keep the code clear, the best practice is to split the data structure part and the parsing part into two modules, respectively `Basic.lean` and `Parser.lean`.

So the file structure may look like:

```sh
.
├── CSVParser.lean
├── CSVParser
│   ├── Basic.lean
│   ├── Parser.lean
│   └── Printer.lean
```

You can also have a separate `Printer` module if you have a complex serialization logic.

It's also recommend group all functions in a separate namespace, namely `namespace CSVParser`.

### User State

If you have some experience of writing parser in Haskell, you will notice that in Lean `Parsec` we cannot have a user state, but that's a design on purpose. We should use the `StateT` transformer to encode the state.

```lean
abbrev StateParsec σ := StateT σ Parsec
```

And current `Parsec` function are automatically lifted from `Parsec` to `StateParsec`, so you can use them as usual.

*NOTE:* the `abbrev` command is required, otherwise you will have to implement `MonadLift` yourself.

### Chanllenge: How to parse CSV homogeneously?

The parser we write above can parse heterogenous CSV files, which we may not want.

```lean
def csvString' : String := "a,\"b\nc\"\r\n1,2\r\n4,5,6"

#eval parse csvString'
-- Except.ok #[#["a", "b\nc"], #["1", "2"], #["4", "5", "6"]]
```

But how can we enforce that the lines are homogeneous?

The answer of the question is provided in [Main.lean](./Main.lean), but please first think of it yourself. 

*HINT:* Also similar to the `many*` series of combinators.

### Further Thinking: How to use `Parsec` on `Stream`?

Streaming is a very important feature for web. Protobuf, GIF, PNG, ..., all these formats are designed to support streaming, and we need a way to streamingly parse them in Lean.

However, the author of this sample cannot provide one. If you have any ideas, please post it in the discussion page of [lean4-samples](https://github.com/leanprover/lean4-samples) :P.

## Other Resources for `Parsec`

You can also look at the example of parsing XML (`Lean.Data.Xml`) and JSON (`Lean.Data.Json`) in Lean core.

The GitHub code search of [language:Lean Parsec](https://github.com/search?q=language%3ALean+Parsec&type=code) is also useful.