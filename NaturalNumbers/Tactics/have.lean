import MyNat.Definition
/-!
# Tactic have

`have h : t := e` adds the hypothesis `h : t` to the current goal if `e` is a term
of type `t`.
* If `t` is omitted, it will be inferred.
* If `h` is omitted, the name `this` is used.
* The variant `have pattern := e` is equivalent to `match e with | pattern => _`,
  and it is convenient for types that have only one applicable constructor.
  For example, given `h : p ∧ q ∧ r`, `have ⟨h₁, h₂, h₃⟩ := h` produces the
  hypotheses `h₁ : p`, `h₂ : q`, and `h₃ : r`.

-/