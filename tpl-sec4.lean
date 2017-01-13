-- https://leanprover.github.io/theorem_proving_in_lean/index.html
-- Section 4 (Quantifiers and Equality)

-- Section 4.1, The Universal Qualifier
section examples1
  variables (α : Type) (p q : α → Prop)

  -- ∀ has very wide scope, hence parenthesis:
  --example : (∀ x : α, p x ∧ q x) → ∀ y : α, p y  :=
  --  assume h : ∀ x : α, p x ∧ q x,
  --  take y : α,
  --  show p y, from (h y)^.left

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

section exercises41a
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

end exercises41a

section exercises41b
  variables (α : Type) (p q : α → Prop)
  variable r : Prop

  example : α → ((∀ x : α, r) ↔ r) :=
    assume a : α, iff.intro
      (assume ar : α → r, ar a)
      (assume hr : r, take α, hr) -- Value doesn't matter

  -- Requires classical reasoning in one direction:
  example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
    iff.intro
      (assume h : ∀ x, p x ∨ r, classical.by_cases
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

end exercises41b

section barber_paradox
  variables (men : Type) (barber : men) (shaves : men → men → Prop)

  -- Lifted this from the prior file:
  variable {p : Prop}
  theorem thm1 : (p → ¬p) → ¬p :=
    assume h : p → ¬p,
    assume h2 : p,
    (h h2) h2
 
  -- Parentheses added to clarify for me
  example (h : (∀ x : men, shaves barber x ↔ ¬ shaves x x)) : false :=
    have h2 : shaves barber barber ↔ ¬shaves barber barber, from h barber,
    have hs : ¬shaves barber barber, from thm1 (iff.mp h2),
    have hns : shaves barber barber, from (iff.mpr h2) hs,
    hs hns
end barber_paradox

-- Section 4.2, Equality

-- Section 4.3, Calculational Proofs
-- (should probably review this later)

-- Section 4.4, The Existential Qualifier
section exercises44a
  variables (α : Type) (p q : α → Prop)
  -- "Notice that the declaration variable a : α amounts to the
  -- assumption that there is at least one element of type α. This
  -- assumption is needed in the second example, as well as in the
  -- last two." (This sounds kinda... nonconstructive.)
  variable a : α
  variable r : Prop

  example : (∃ x : α, r) → r :=
    (assume h : (∃ x : α, r),
      exists.elim h
        (assume α, assume r, r))

  -- Or:
  example : (∃ x : α, r) → r :=
    (assume h : (∃ x : α, r),
      match h with ⟨w, hw⟩ := 
        hw
      end)

  -- Or (by implicit match):
  example : (∃ x : α, r) → r := assume ⟨x, hr⟩, hr

  example : r → (∃ x : α, r) :=
    assume hr : r,
    exists.intro a hr

  -- Or:
  example : r → (∃ x : α, r) := assume hr : r, ⟨a, hr⟩

  example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
    iff.intro
      (assume h : ∃ x, p x ∧ r, exists.elim h
        (take a : α, assume hpr : p a ∧ r,
          and.intro ⟨a, and.left hpr⟩ (and.right hpr)))
      (assume h : (∃ x, p x) ∧ r, and.elim h
        (assume hp : ∃ x, p x, assume hr : r,
          match hp with ⟨x, hp2⟩ :=
            ⟨x, and.intro hp2 hr⟩
          end))

  -- Or (match on ((∃ x, p x) ∧ r) is outer-first):
  example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := iff.intro
      (assume ⟨(x : α), (hp : p x), (hr : r)⟩, and.intro ⟨x, hp⟩ hr)
      (assume ⟨⟨x, hp⟩, hr⟩, ⟨x, and.intro hp hr⟩)

  example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := iff.intro
    (assume ⟨x, (h : p x ∨ q x)⟩, or.elim h
      (assume hp : p x, or.inl ⟨x, hp⟩)
      (assume hq : q x, or.inr ⟨x, hq⟩))
    (assume h : (∃ x, p x) ∨ (∃ x, q x), or.elim h
      (assume ⟨x, hp⟩, ⟨x, or.inl hp⟩)
      (assume ⟨x, hq⟩, ⟨x, or.inr hq⟩))

  -- I guess this relies on classical reasoning.  ¬(∃x, ¬p x) only
  -- says that no x exists for which ¬p x - which doesn't
  -- (constructively) say that any x exists for which p x, much less
  -- that all x have that property.
  example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
    iff.intro
      (assume h : ∀ (x : α), p x,
        assume ⟨(x : α), (np : ¬p x)⟩, np (h x))
      (assume h : ¬∃ (x : α), ¬p x,
        take x, classical.by_contradiction
          -- Assume that some x *does* exist for which ¬p x, and we
          -- contradict ¬(∃x, ¬p x):
          (assume np : ¬p x, h ⟨x, np⟩))

-- Various exercises below are still incomplete:

  example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
    iff.intro
      (assume ⟨(x : α), (px : p x)⟩,
        -- Witness 'x' disproves ∀x, ¬p x:
        assume h : ∀ (x : α), ¬p x, (h x) px)
      (assume hn : ¬∀ (x : α), ¬p x,
        -- (¬∀x, ¬p x) = (∀x, ¬p x) → false, that is, we can't show
        -- that every 'x' produces ¬p x... but if I'm understanding
        -- this right, this can't tell us which 'x' has that property,
        -- thus it can't be shown constructively.
        sorry
        -- but I can't figure out how to show it with classical
        -- reasoning either!
        )

  example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
    iff.intro
      (assume hn : ¬ ∃ x, p x,
        take x, assume h : p x, hn ⟨x, h⟩)
      (assume h : ∀ x, ¬ p x,
        -- If ¬p x for all x, then any x for which p x must be a
        -- contradiction:
        assume ⟨(x : α), (hp : p x)⟩, (h x) hp)

  example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
    iff.intro
      (assume h : ¬ ∀ x, p x, sorry)
      (assume ⟨x, (nhp : ¬ p x)⟩,
        assume hp : ∀ x, p x, nhp (hp x))

  example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
    iff.intro
      (assume h : ∀ x, p x → r,
        assume ⟨(x : α), (hp : p x)⟩, (h x) hp)
      (assume h : (∃ x, p x) → r, take x,
        assume hp : p x, h ⟨x, hp⟩)

  example : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
    iff.intro
      (assume ⟨x, (hp : p x → r)⟩,
        assume h : (∀ (x : α), p x), hp (h x))
      (assume h : (∀ x, p x) → r, sorry)

  example : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
    iff.intro
      (assume ⟨x, (f : r → p x)⟩, assume hr : r, ⟨x, f hr⟩)
      (assume h : (r → ∃ x, p x),
        or.elim (classical.em r)
          (assume hr : r,
            match h hr with ⟨x, px⟩ :=
              ⟨x, assume r, px⟩
            end)
          (assume hr : ¬r, sorry))

end exercises44a
