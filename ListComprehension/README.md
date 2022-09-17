# List Comprehension with Syntax Extensions

For those of you who are addicted to the really cool
[list comprehension features of Python](https://docs.python.org/3/tutorial/datastructures.html),
you might be looking for something similar in Lean.

First you need to understand that the Lean `List` is a `Functor`.
See [reference manual documentation on Functors](https://leanprover.github.io/lean4/doc/monads/functors.lean.html) which explains the `map` function that can transform a list as follows:

```lean
#eval List.map (λ x => toString x) [1,2,3]
-- ["1", "2", "3"]
```

which can also be written using dot notation:

```lean
#eval [1,2,3,4,5,6,7].map (λ x => x + 1)
-- [2, 3, 4, 5, 6, 7, 8]
```

And again using the `<$>` notation:

```lean
#eval (λ x => x + 1) <$> [1,2,3,4,5,6,7]
-- [2, 3, 4, 5, 6, 7, 8]
```

So one of the first examples from the Python documentation is to
simply square the values of a list containing the range 0-9:

```lean
#eval (List.range 10).map (λ x => x * x)
-- [0, 1, 4, 9, 16, 25, 36, 49, 64, 81]
```

There is [sugar syntax](https://leanprover.github.io/lean4/doc/functions.html?highlight=sugar#syntax-sugar-for-simple-lambda-expressions) for lambda functions
which allows the above to be written more compactly as:

```lean
#eval (List.range 10).map (· ^ 2)
-- [0, 1, 4, 9, 16, 25, 36, 49, 64, 81]
```
But the next python example does not work in Lean until we teach Lean some new tricks.

```python
[(x, y) for x in [1,2,3] for y in [3,1,4] if x != y]
# [(1, 3), (1, 4), (2, 3), (2, 1), (2, 4), (3, 1), (3, 4)]
```

Lean allows you to extend the syntax of the language using
[macros](https://leanprover.github.io/lean4/doc/macro_overview.html).  In Lean a macro
is a function that takes in a syntax tree and produces a new syntax tree.

The following syntax extension adds some list comprehension capabilities to lean.
Many thanks to Kyle Miller who first posted this solution on [Zulip](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/List.20Functor):

```lean
declare_syntax_cat compClause
syntax "for " term " in " term : compClause
syntax "if " term : compClause

syntax "[" term " | " compClause,* "]" : term

def List.map' (xs : List α) (f : α → β) : List β := List.map f xs

macro_rules
  | `([$t:term |]) => `([$t])
  | `([$t:term | for $x in $xs]) => `(List.map' $xs  (λ $x => $t))
  | `([$t:term | if $x]) => `(if $x then [$t] else [])
  | `([$t:term | $c, $cs,*]) => `(List.join [[$t | $cs,*] | $c])

def List.prod (xs : List α) (ys : List β) : List (α × β) := [(x, y) | for x in xs, for y in ys]
```

So for example, you can use this to implement the above python list comprehension:

```lean
#eval [(x, y) | for x in [1,2,3], for y in [3,1,4], if x != y]
-- [(1, 3), (1, 4), (2, 3), (2, 1), (2, 4), (3, 1), (3, 4)]
```

The difference with python is that you need a vertical bar `|` to separate the term
that computes the items in the list from the `for` loops and `if` test conditions
and you need a comma separating each of those comprehension clauses.

Continuing on with more examples from the python documentation we have this one
which creates a new list with the values doubled:

```lean
def vec : List Int := [-4, -2, 0, 2, 4]
#eval [x*2 | for x in vec]
-- [-8, -4, 0, 4, 8]
```

The next one cannot be done with the `map` function because the result is a different
sized list, it filters the list to exclude negative numbers:

```lean
#eval [x | for x in vec, if x >= 0]
-- [0, 2, 4]
```

You can apply a function to all the elements, here we convert the numbers
to positive numbers:

```lean
#eval [x.natAbs | for x in vec]
-- [4, 2, 0, 2, 4]
```

And you can call a method on each element using dot notation:

```lean
def freshfruit := ["  banana", "  loganberry ", "passion fruit  "]

#eval [weapon.trim | for weapon in freshfruit]
-- ["banana", "loganberry", "passion fruit"]
```

You can create a list of pairs like (number, square):

```lean
#eval [(x, x^2) | for x in List.range 6]
-- [(0, 0), (1, 1), (2, 4), (3, 9), (4, 16), (5, 25)]
```

and you can flatten a list using two 'for' clauses where the first walks the
3 top level lists, and the second walks the elements in each one of those lists:

```lean
def nested := [[1,2,3], [4,5,6], [7,8,9]]
#eval [num | for elem in nested, for num in elem]
-- [1, 2, 3, 4, 5, 6, 7, 8, 9]
```

Of course the term on the left of the vertical bar can be any complex expression, in this
example we use a `let` expression to compute i * pi, we then round that and convert
the result to a string.

```lean
def pi := 3.1415926535
#eval [let x := i.toFloat * pi; toString (Float.round x) | for i in List.range 6]
-- ["0.000000", "3.000000", "6.000000", "9.000000", "13.000000", "16.000000"]
```

## Nested Comprehensions

You can also do nested list comprehensions.
Since the initial expression in a list comprehension can be any arbitrary expression, it
can also be another list comprehension.
Consider the following example of a 3x4 matrix implemented as a list of 3 lists of length 4:

```lean
def matrix := [
    [1, 2, 3, 4],
    [5, 6, 7, 8],
    [9, 10, 11, 12]]
```

The following list comprehension will transpose rows and columns:

```lean
#eval [[row[i]! | for row in matrix] | for i in List.range 4]
--[[1, 5, 9], [2, 6, 10], [3, 7, 11], [4, 8, 12]]
```

Note that the exclamation mark `!` is needed to tell Lean that the list index
is "safe".  Note also that the square bracket random access on list is very
inefficient, each access is an entire walk of the elements of the list to that
location.  It would be better to implement this sort of thing using Lean Arrays.

## List product

You can define the following function that computes all combinations of elements from two
lists:

```lean
def List.prod (xs : List α) (ys : List β) : List (α × β) := [(x, y) | for x in xs, for y in ys]
```

For example:

```lean
#eval List.prod (List.range 3) (List.range 3)
-- [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
```

Which means you can do some fun things like multiply the values in these pairs:
```lean
#eval [x * y | for (x, y) in List.prod (List.range 3) (List.range 3)]
-- [0, 0, 0, 0, 1, 2, 0, 2, 4]
```

Or filter the list to pairs that add up to numbers greater than 3 and less than or equal to 5:
```lean
#eval [(x, y) | for x in List.range 5, for y in List.range 5, if x + y <= 5 && x + y > 3]
-- [(0, 4), (1, 3), (1, 4), (2, 2), (2, 3), (3, 1), (3, 2), (4, 0), (4, 1)]
```

## Syntax Extension

How does the syntax extension work?

The syntax extension adds a new syntax category for the "comprehension clauses"
called `compClause` using:
```lean
declare_syntax_cat compClause
```

Then it defines a `for * in *` syntax parser that results in a `compClause`
```lean
syntax "for " term " in " term : compClause
```
And another syntax parser for the `if term` we want to allow in a `compClause` :

```lean
syntax "if " term : compClause
```

Then we want to allow a list syntax with a vertical bar separating the comprehension
term from a comma separated list of zero or more compClauses:

```lean
syntax "[" term " | " compClause,* "]" : term
```

This results in a `term` that can then be used in a macro which will act as our
syntax transformer:

```lean
macro_rules
  | `([$t:term |]) => `([$t])
  | `([$t:term | for $x in $xs]) => `(List.map' $xs  (λ $x => $t))
  | `([$t:term | if $x]) => `(if $x then [$t] else [])
  | `([$t:term | $c, $cs,*]) => `(List.join [[$t | $cs,*] | $c])
```

This macro lists a set of patterns to match, where the `=>` side is pointing to the output we want
the syntax transformed into.  So the first one is the case with no `compClause`, which just becomes
a simple list containing the term. You can test this works with something like `#eval [10 | ]` which
produces the list `[10]`.

The second pattern handles the for loop `compClause` which transforms to the `List.map` functor,
here we've defined a slight variation on the `List.map` named `List.map'` which simply reverses the
order of the args. This helps Lean type inference work better over all the clauses.

The third pattern handles the `if` condition which transforms to a complete Lean `if then else`
expression where the else clause simply returns an empty list.

The fourth pattern handles multiple `compClauses` separated by commas.  This is recursive in nature
because the expansion on the right includes two nested list comprehensions, the inner one `[$t |
$cs,*]` and the outer one `[[$t | $cs,*] | $c]` and these will trigger more macro expansions, and
Lean will keep expanding these until they are all done.  Since this nested expansion results in
nested lists it uses `List.join` to flatten those back into a single list.

So let's pick the following example apart and see how it works:

```lean
def nested := [[1,2,3], [4,5,6], [7,8,9]]

#eval [num | for elem in nested, for num in elem, if num < 5]
```

This matches the comma separated syntax, with 3 clauses, which expands to
`List.join [[$t | $cs,*] | $c])` where `$t` is `num` and `$cs,*` is the tail `for num in elem, if num < 5`
and `$c` is `for elem in nested`, so we have this first expansion:

```lean
#eval List.join [[num | for num in elem, if num < 5] | for elem in nested]
-- [1, 2, 3, 4]
```

Now the inner comprehension with a for loop and and if-expression expands to this,
here we are testing it on the first `elem` in `nested`:

```lean
#eval List.map' [1,2,3] (λ num => if num < 5 then [num] else [])
-- [[1], [2], [3]]
```

Which the List.join flattens:
```lean
#eval List.join (List.map' [1,2,3] (λ num => if num < 5 then [num] else []))
-- [1, 2, 3]
```

The outer comprehension `for elem in nested` adds an outer `List.map'` over this the `nested` list
of lists:

```lean
#eval List.map' nested  (λ elem =>
        List.join (List.map' elem (λ num => if num < 5 then [num] else []) ))
-- [[1, 2, 3], [4], []]
```

Which is finished with a final `List.join` to get our expected result:
```lean
#eval List.join (List.map' nested  (λ elem =>
        List.join (List.map' elem (λ num => if num < 5 then [num] else []) )))
-- [1, 2, 3, 4]
```

So as you can see with this example, the syntax extension feature of Lean is very powerful.
Lean's implementation of macro expansion is called [hyghienic](https://en.wikipedia.org/wiki/Hygienic_macro) because it is guaranteed not to cause the accidental capture of identifiers.