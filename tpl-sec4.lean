
-- https://leanprover.github.io/theorem_proving_in_lean/index.html
-- Section 4 (Quantifiers and Equality)

section examples1
  variables (α : Type) (p q : α → Prop)

  -- ∀ has very wide scope, hence parenthesis:
  example : (∀ x : α, p x ∧ q x) → ∀ y : α, p y  :=
    assume h : ∀ x : α, p x ∧ q x,
    take y : α,
    show p y, from (h y)^.left

  -- Equivalent (it's just renaming of bound variables):
  example : (∀ x : α, p x ∧ q x) → ∀ y : α, p y  :=
    assume h : ∀ x : α, p x ∧ q x,
    take z : α,
    show p z, from and.elim_left (h z)
end examples1

section examples2
  variables (α : Type) (r : α → α → Prop)
  variable trans_r : ∀ x y z, r x y → r y z → r x z

  variables (a b c : α)
  variables (hab : r a b) (hbc : r b c)

  check trans_r
  check trans_r a b c
  check trans_r a b c hab
  check trans_r a b c hab hbc
end examples2

section examples3
  variables (α : Type) (r : α → α → Prop)
  -- x, y, z can be implicit instead, to avoid passing them explicitly
  -- when they can simply be inferred:
  variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

  variables (a b c : α)
  variables (hab : r a b) (hbc : r b c)

  -- Note the ?M_1, ?M_2, ?M_3 in the below.  These are far cases
  -- where Lean cannot infer the types.
  check trans_r
  check trans_r hab
  check trans_r hab hbc

  variable refl_r : ∀ x, r x x
  variable symm_r : ∀ {x y}, r x y → r y x

  -- Reasoning with transitivity & symmetry:
  example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
    trans_r (trans_r hab (symm_r hcb)) hcd  
end examples3

section exercises1
  variables (α : Type) (p q : α → Prop)

  example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
    iff.intro
      (assume h : ∀ x, p x ∧ q x,
        and.intro
        (take x : α, and.left  (h x))
        (take x : α, and.right (h x)))
      (assume h : (∀ x, p x) ∧ (∀ x, q x),
        take x : α, and.elim h
          (assume h1 : ∀ (x : α), p x,
           assume h2 : ∀ (x : α), q x,
           and.intro (h1 x) (h2 x)))

  example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
    assume h1 : ∀ x, p x → q x,
    assume h2 : ∀ x, p x,
    take x : α, h1 x (h2 x)

  -- "You should also try to understand why the reverse implication is
  -- not derivable in the last example."
  example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
    assume h : (∀ x, p x) ∨ (∀ x, q x),
    take x : α, or.elim h
      (assume h2 : ∀ (x : α), p x, or.inl (h2 x))
      (assume h2 : ∀ (x : α), q x, or.inr (h2 x))

  -- Reverse implication:
  open classical
  example : (∀ x, p x ∨ q x) → (∀ x, p x) ∨ (∀ x, q x) :=
    assume h : ∀ x, p x ∨ q x,
    show (∀ (x : α), p x) ∨ (∀ (x : α), q x), from sorry
    -- I suppose it can't be derived because... (∀x, p x ∨ q x) tells
    -- us only that, for all (x : α), one of (p x) or (q x) is true.
    -- It doesn't say which, and further, that may depend on x.
    -- However, to construct (∀x, p x) ∨ (∀x, q x), we must choose a
    -- side, but can't guarantee that the 'x' of one side is the same
    -- as the other.
    -- 
    -- For an example, suppose that x is a natural number, p checks
    -- for even numbers, and q checks for odd numbers.  (∀x, p x ∨ q
    -- x) is clearly true - every single x must be either even or odd.
    -- However, (∀x, p x) and (∀x, q x) are both false - not all
    -- numbers are even, and not all numbers are odd. Since neither
    -- one is true, (∀x, p x) ∨ (∀x, q x) must be false also.

  -- If we had (∀x, p x ∧ q x) (note ∧ rather than ∨), then we
  -- should be able to derive (∀ x, p x) ∨ (∀ x, q x) because we now
  -- know that both (p x) and (q x) are true, regardless of x.
  example : (∀ x, p x ∧ q x) → (∀ x, p x) ∨ (∀ x, q x) :=
    assume h : ∀ x, p x ∧ q x,
    or.inl (take x : α, and.left (h x))
  -- or:
  example : (∀ x, p x ∧ q x) → (∀ x, p x) ∨ (∀ x, q x) :=
    assume h : ∀ x, p x ∧ q x,
    or.inr (take x : α, and.right (h x))

end exercises1

section exercises2
  open classical
  variables (α : Type) (p q : α → Prop)
  variable r : Prop

  example : α → ((∀ x : α, r) ↔ r) :=
    assume a : α, iff.intro
      (assume ar : α → r, ar a)
      (assume hr : r, take α, hr) -- Value doesn't matter

  -- Requires classical reasoning in one direction:
  example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
    iff.intro
      (assume h : ∀ x, p x ∨ r, by_cases -- uses EM here
          or.inr
          (assume hnr : ¬r,
            or.inl (take x : α, or.resolve_right (h x) hnr)))
      (assume h : (∀ x, p x) ∨ r,
        or.elim h
          (assume h2 : ∀ x, p x,
            take x, or.inl (h2 x))
          (assume h2 : r,
            take x, or.inr h2))
  
  example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
    iff.intro
      (assume h : ∀ x, r → p x, assume hr : r, take x : α,    h x  hr)
      (assume h : r → ∀ x, p x, take x : α,    assume hr : r, h hr x)

end exercises2
