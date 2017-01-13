-- https://leanprover.github.io/theorem_proving_in_lean/index.html
-- Section 5 (Tactics)

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
begin
  apply and.intro,
  exact hp,
  apply and.intro,
  exact hq,
  exact hp
end
print test
-- This looks very Coq-like to me (perhaps intentionally, since Roesch
-- spoke very highly of Coq's tactics as something that Idris and Agda
-- were missing).

-- Helpful:
-- "You can write a tactic script incrementally. If you run Lean on an
-- incomplete tactic proof bracketed by begin and end, the system
-- reports all the unsolved goals that remain. If you are running Lean
-- with its Emacs interface, you can see this information by putting
-- your cursor on the end symbol, which should be underlined. In the
-- Emacs interface, there is another extremely useful trick: if you
-- put your cursor on a line of a tactic proof and press "C-c C-g",
-- Lean will show you the goal that remains at the end of the line."

-- Equivalent:
theorem test2 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
begin
  apply and.intro hp,
  exact and.intro hq hp
end
print test2

-- Also equivalent:
theorem test3 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
by exact and.intro hp (and.intro hq hp)
print test3

section example1
  variables {p q : Prop} (hp : p) (hq : q)

  include hp hq

  example : p ∧ q ∧ p :=
  begin
    apply and.intro hp,
    exact and.intro hq hp
  end  
end example1

-- "We adopt the following convention regarding indentation: whenever
-- a tactic introduces one or more additional subgoals, we indent
-- another two spaces, until the additional subgoals are deleted."
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  apply iff.intro,
    intro h, -- 1st subgoal (iff.intro)
    apply or.elim (and.elim_right h),
      intro hq, -- 1st subsubgoal
      apply or.intro_left,
      apply and.intro, -- 2 subsubsubgoals:
        exact and.elim_left h,
      exact hq,
    intro hr, -- 2nd subsubgoal
    apply or.intro_right,
    apply and.intro, -- 2 subsubsubgoals:
      exact and.elim_left h,
      exact hr,
  intro h,  -- 2nd subgoal (iff.intro)
  apply or.elim h,
    intro hpq,
    apply and.intro,
      exact and.elim_left hpq,
    apply or.intro_left,
    exact and.elim_right hpq,
  intro hpr,
  apply and.intro,
    exact and.elim_left hpr,
  apply or.intro_right,
  exact and.elim_right hpr
end

section example_assumption
  variables {x y z w : Prop}
  example (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w :=
  begin
    apply eq.trans h₁,
    apply eq.trans h₂,
    assumption   -- applied h₃
  end

  example (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w :=
  begin
    apply eq.trans,
    assumption,     -- solves x = ?m_1 with h₁
    apply eq.trans,
    assumption,     -- solves y = ?m_1 with h₂
    assumption      -- solves z = w with h₃
  end
end example_assumption

example : ∀ a b c : ℕ, a = b → a = c → c = b :=
begin
  intros,
  apply eq.trans,
  apply eq.symm,
  assumption,
  assumption
end

-- Same as previous:
example : ∀ a b c : ℕ, a = b → a = c → c = b :=
begin
  intros,
  transitivity,
  symmetry,
  assumption,
  assumption
end

-- Or:
example : ∀ a b c : ℕ, a = b → a = c → c = b :=
begin
  intros,
  transitivity,
  symmetry,
  repeat { assumption }
end

example : ∃ a : ℕ, a = a :=
begin
  fapply exists.intro,
  exact 0,
  apply rfl
end

section example_generalize
  variables x y z : ℕ

  example : x = x :=
  begin
    generalize x z, -- goal is x : ℕ ⊢ ∀ (z : ℕ), z = z
    intro y,      -- goal is x y : ℕ ⊢ y = y
    reflexivity
  end  

  -- I still don't totally get this...
  example : x + y + z = x + y + z :=
  begin
    generalize (x + y + z) w, -- goal is x y z : ℕ ⊢ ∀ (w : ℕ), w = w
    intro u,                  -- goal is x y z u : ℕ ⊢ u = u
    reflexivity
  end

  example : x + y + z = x + y + z :=
  begin
    generalize (x + y + z) w, -- goal is x y z : ℕ ⊢ ∀ (w : ℕ), w = w
    clear x y z,
    intro u,                  -- goal is u : ℕ ⊢ u = u
    reflexivity
  end
end example_generalize

example (x : ℕ) : x = x :=
begin
  revert x,     -- goal is ⊢ ∀ (x : ℕ), x = x
  intro y,      -- goal is y : ℕ ⊢ y = y
  reflexivity
end

-- "Moving a hypothesis into the goal yields an implication:" (Is it
-- sort of the opposite of 'intro' then?)
example (x y : ℕ) (h : x = y) : y = x :=
begin
  revert h,     -- goal is x y : ℕ ⊢ x = y → y = x
  intro h₁,     -- goal is x y : ℕ, h₁ : x = y ⊢ y = x
  symmetry,
  assumption
end

-- "reverting x in the example above brings h along with it:"
example (x y : ℕ) (h : x = y) : y = x :=
begin
  revert x,     -- goal is y : ℕ ⊢ ∀ (x : ℕ), x = y → y = x
  intros,
  symmetry,
  assumption
end

example (x y : ℕ) (h : x = y) : y = x :=
begin
  revert x y,     -- goal is ⊢ ∀ (x y : ℕ), x = y → y = x
  intros,
  symmetry,
  assumption
end

-- to create disjunction: left = apply or.inl, right = apply or.inr
-- to decompose disjunction: 'cases' tactic
example (p q : Prop) : p ∨ q → q ∨ p :=
begin
  intro h,
  cases h with hp hq,
  -- case hp : p
  right, exact hp,
  -- case hq : q
  left, exact hq
end

example (p q : Prop) : p ∧ q → q ∧ p :=
begin
  intro h,
  -- Also works for conjunction (or any inductively-defined type):
  cases h with hp hq,
  -- 'constructor' applies first constructor of inductive type (first?
  -- what?)
  constructor, exact hq, exact hp
end

section swap
  universe variables u v
  
  def swap_pair {α : Type u} {β : Type v} : α × β → β × α :=
  begin
    intro p,
    cases p with ha hb,
    constructor, exact hb, exact ha
  end
  
  def swap_sum {α : Type u} {β : Type v} : α ⊕ β → β ⊕ α :=
  begin
    intro p,
    cases p with ha hb,
      right, exact ha,
      left, exact hb
  end
end swap

section nats
  open nat

  example (P : ℕ → Prop) (h₀ : P 0) (h₁ : ∀ n, P (succ n)) (m : ℕ) : P m :=
  begin
    cases m with m', exact h₀, exact h₁ m'
  end
end nats

-- My term-style solution (from section 3):
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  iff.intro
    (assume h : p ∧ (q ∨ r),
      (show (p ∧ q) ∨ (p ∧ r), from
        and.elim h
          (assume hp : p, assume hqr : q ∨ r,
            or.elim hqr
              (assume hq : q, or.inl (and.intro hp hq))
              (assume hr : r, or.inr (and.intro hp hr)))))
    (assume h : (p ∧ q) ∨ (p ∧ r),
      (show p ∧ (q ∨ r), from
        or.elim h
          (assume hpq : (p ∧ q),
            have hp : p, from and.left hpq,
            have hqr : q ∨ r, from or.inl (and.right hpq),
            and.intro hp hqr)
          (assume hpr : (p ∧ r),
            have hp : p, from and.left hpr,
            have hqr : q ∨ r, from or.inr (and.right hpr),
            and.intro hp hqr)))


-- Their tactic-style solution:
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  apply iff.intro,
  intro h,
   cases h with hp hqr,
   cases hqr with hq hr,
     left, constructor, repeat { assumption },
     right, constructor, repeat { assumption },
  intro h,
    cases h with hpq hpr,
      cases hpq with hp hq,
        constructor, exact hp, left, exact hq,
      cases hpr with hp hr,
        constructor, exact hp, right, exact hr
end

-- Their solution combining both styles:
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  apply iff.intro,
    intro h,
    cases h^.right with hq hr,
      exact
        show (p ∧ q) ∨ (p ∧ r),
          from or.inl ⟨h^.left, hq⟩,
    exact
      show (p ∧ q) ∨ (p ∧ r),
        from or.inr ⟨h^.left, hr⟩,
  intro h,
  cases h with hpq hpr,
    exact
      show p ∧ (q ∨ r),
        from ⟨hpq^.left, or.inl hpq^.right⟩,
  exact show p ∧ (q ∨ r),
    from ⟨hpr^.left, or.inr hpr^.right⟩
end
-- "One thing that is nice about Lean's proof-writing syntax is that
-- it is possible to mix term-style and tactic-style proofs, and pass
-- between the two freely. For example, the tactics apply and exact
-- expect arbitrary terms, which you can write using have, show, and
-- so on. Conversely, when writing an arbitrary Lean term, you can
-- always invoke the tactic mode by inserting a begin...end block. "

-- Even further, using "show p, from t" for "exact (show p, from t)":
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  apply iff.intro,
    intro h,
    cases h^.right with hq hr,
      show (p ∧ q) ∨ (p ∧ r),
        from or.inl ⟨h^.left, hq⟩,
    show (p ∧ q) ∨ (p ∧ r),
      from or.inr ⟨h^.left, hr⟩,
  intro h,
  cases h with hpq hpr,
    show p ∧ (q ∨ r),
      from ⟨hpq^.left, or.inl hpq^.right⟩,
  show p ∧ (q ∨ r),
    from ⟨hpr^.left, or.inr hpr^.right⟩
end

-- Further still, using "have p, from t₁, t₂" for
-- "exact (have p, from t₁, t₂)":
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
begin
  intro h,
  have hp : p, from h^.left,
  have hqr : q ∨ r, from h^.right,
  show (p ∧ q) ∨ (p ∧ r),
  begin
    cases hqr with hq hr,
      exact or.inl ⟨hp, hq⟩,
    exact or.inr ⟨hp, hr⟩
  end
end

-- { & } act like nested begin/end:
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  apply iff.intro,
  { intro h,
    cases h^.right with hq hr,
    { show (p ∧ q) ∨ (p ∧ r),
        from or.inl ⟨h^.left, hq⟩ },
    show (p ∧ q) ∨ (p ∧ r),
      from or.inr ⟨h^.left, hr⟩ },
  intro h,
  cases h with hpq hpr,
  { show p ∧ (q ∨ r),
      from ⟨hpq^.left, or.inl hpq^.right⟩ },
  show p ∧ (q ∨ r),
    from ⟨hpr^.left, or.inr hpr^.right⟩
end
-- Note that an unsolved goal at "end" (or a closing bracket)
-- generates an error; use this to keep goals lined up.

-- Their convention: "every time a tactic leaves more than one
-- subgoal, we separate the remaining subgoals by enclosing them in
-- blocks and indenting, until we are back down to one subgoal" Note
-- that this differs a bit from what one might naturally expect,
-- e.g. indenting all subgoals including the last.

example (p q : Prop) : p ∧ q ↔ q ∧ p :=
begin
  apply iff.intro,
  { intro h,
    -- 'assert' creates subgoals, and the term hangs around in the
    -- context after that subgoal is proved:
    assert hp : p, exact h^.left,
    assert hq : q, exact h^.right,
    exact ⟨hq, hp⟩ },
  intro h,
  assert hp : p, exact h^.right,
  assert hq : q, exact h^.left,
  exact ⟨hp, hq⟩
end

-- Another way ('note' inserts a fact into the context):
example (p q : Prop) : p ∧ q ↔ q ∧ p :=
begin
  apply iff.intro,
  { intro h,
    note hp := h^.left,
    note hq := h^.right,
    exact ⟨hq, hp⟩ },
  intro h,
  note hp := h^.right,
  note hq := h^.left,
  exact ⟨hp, hq⟩
end
-- But with 'note' you can't get at the contents (not totally sure
-- what this means), whereas with 'pose' you can:
example : ∃ x : ℕ, x + 3 = 8 :=
begin
  pose x := 5,
  existsi x,
  reflexivity
end

example (p q : Prop) : p ∧ q → q ∧ p :=
begin
  intro h,
  split,
  { change q,
    -- I don't understand the point of 'change' here.  I can remove it
    -- and not change anything.
    exact h^.right },
  change p,
  exact h^.left
end

example (a b : ℕ) (h : a = b) : a + 0 = b + 0 :=
begin
  change a = b,
  assumption
end

example (a b c : ℕ) (h₁ : a = b) (h₂ : b = c) : a = c :=
begin
  transitivity,
    change _ = b, assumption,
  assumption
end
-- "In this example, after the transitivity tactic is applied, there
-- are two goals, a = ?m_1 and ?m_1 = c. After the change, the two
-- goals have been specialized to a = b and b = c."

section rewrite1
  variables (f : ℕ → ℕ) (k : ℕ)
  
  example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 :=
  begin
    rw h₂, -- replace k with 0
    rw h₁  -- replace f 0 with 0
  end

  -- Identical:
  example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 :=
  begin
    rw [h₂, h₁]
  end
end rewrite1

section rewrite2
  variables (f : ℕ → ℕ) (a b : ℕ)
  
  example (h₁ : a = b) (h₂ : f a = 0) : f b = 0 :=
  begin
    -- Rewriting in reverse direction of equality (see minus sign):
    rw [-h₁, h₂]
  end
end rewrite2

-- Clarifying a rewrite with an argument:
example (a b c : ℕ) : a + b + c = a + c + b :=
begin
  rw [add_assoc, add_comm b, -add_assoc]
end

example (a b c : ℕ) : a + b + c = a + c + b :=
begin
  rw [add_assoc, add_assoc, add_comm b]
end

example (a b c : ℕ) : a + b + c = a + c + b :=
begin
  rw [add_assoc, add_assoc, add_comm _ b]
end

-- Applying to specific hypothesis:
section rewrite3
  variables (f : ℕ → ℕ) (a : ℕ)
  
  example (h : a + 0 = 0) : f a = f 0 :=
  begin
    rw add_zero at h, rw h
  end
end rewrite3

section rewrite4
  universe variable u
  
  def tuple (α : Type u) (n : ℕ) := { l : list α // list.length l = n }
  
  variables {α : Type u} {n : ℕ}
  
  -- Note that propositions are just types, and 'rewrite' can work
  -- more generally on types other than Prop:
  example (h : n = 0) (t : tuple α n) : tuple α 0 :=
  begin
    rw h at t,
    exact t
  end
end rewrite4

-- Examples of 'simp' (much more automated than 'rewrite'):
section simplify1
  variables (x y z : ℕ) (p : ℕ → Prop)
  premise   (h : p (x * y))
  
  example : (x + 0) * (0 + y * 1 + z * 0) = x * y :=
  by simp
  
  include h
  example : p ((x + 0) * (0 + y * 1 + z * 0)) :=
  begin simp, assumption end

  -- Simplify a hypothesis:
  example (h : p ((x + 0) * (0 + y * 1 + z * 0))) : p (x * y) :=
  begin simp at h, assumption end
end simplify1

-- Exercises I should probably do myself: Redo some of the section 4
-- exercises in tactic style rather than term style.

