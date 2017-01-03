-- Notes/exercises from:
-- https://leanprover.github.io/theorem_proving_in_lean/index.html
-- Section 3 (Propositions and Proofs)

open classical

variables p q r s : Prop

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  iff.intro
  -- Written out a little more verbosely so I can test some things:
  (assume h : p ∧ q,
    have hp : p, from and.left h,
    have hq : q, from and.right h,
    show q ∧ p, from and.intro hq hp)
  (assume h : q ∧ p,
    have hq : q, from and.left h,
    have hp : p, from and.right h,
    show p ∧ q, from and.intro hp hq)

example : p ∨ q ↔ q ∨ p :=
  iff.intro
  (assume h : p ∨ q, 
    or.elim h (assume hp : p, show q ∨ p, from or.inr hp)
              (assume hq : q, show q ∨ p, from or.inl hq))
  (assume h : q ∨ p,
    or.elim h (assume hq : q, show p ∨ q, from or.inr hq)
              (assume hp : p, show p ∨ q, from or.inl hp))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  iff.intro
    (assume hpqr : (p ∧ q) ∧ r,
      have hr : r, from and.right hpqr,
      have hpq : p ∧ q, from and.left hpqr,
      have hp : p, from and.left hpq,
      have hq : q, from and.right hpq,
      show p ∧ (q ∧ r), from and.intro hp (and.intro hq hr))
    (assume hpqr : p ∧ (q ∧ r), 
      have hp : p, from and.left hpqr,
      have hqr : q ∧ r, from and.right hpqr,
      have hq : q, from and.left hqr,
      have hr : r, from and.right hqr,
      show (p ∧ q) ∧ r, from and.intro (and.intro hp hq) hr)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  iff.intro
    (assume hpqr : (p ∨ q) ∨ r, 
      or.elim hpqr
        (assume hpq : p ∨ q,
          or.elim hpq
            (assume hp : p, or.inl hp)
            -- Now I see how 'show' is just an annotation:
            (assume hq : q, show p ∨ (q ∨ r), from or.inr (or.inl hq)))
        (assume hr : r, or.inr (or.inr hr)))
    (assume hpqr : p ∨ (q ∨ r),
      or.elim hpqr
        (assume hp : p, or.inl (or.inl hp))
        (assume hqr : q ∨ r,
          or.elim hqr
            (assume hq : q, or.inl (or.inr hq))
            (assume hr : r, or.inr hr)))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
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

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  iff.intro
    (assume h : p ∨ (q ∧ r),
      (show (p ∨ q) ∧ (p ∨ r), from
        or.elim h
          (assume hp : p,
            and.intro (or.inl hp) (or.inl hp))
          (assume hqr : q ∧ r,
            and.elim hqr
              (assume hq : q, assume hr : r,
                and.intro (or.inr hq) (or.inr hr)))))
    (assume h : (p ∨ q) ∧ (p ∨ r), 
      (show (p ∨ (q ∧ r)), from
        and.elim h
          (assume pq : p ∨ q, assume pr : p ∨ r,
            or.elim pq
              (assume hp : p, or.inl hp)
              (assume hq : q, 
                or.elim pr
                  -- I feel like this part could possibly be simpler,
                  -- but then, this branch of or.elim doesn't
                  -- guarantee ¬p (it's not exclusive or)
                  (assume hp2 : p, or.inl hp2)
                  (assume hr : r, or.inr (and.intro hq hr))))))

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  iff.intro
    (assume h : p → (q → r),
      assume hpq : p ∧ q,
        have hp : p, from and.left hpq,
        have hq : q, from and.right hpq,
        (h hp) hq)
    (assume h : p ∧ q → r,
      assume hp : p,
      assume hq : q,
      have pq : p ∧ q, from and.intro hp hq,
      h pq)

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  iff.intro
    (assume h : (p ∨ q) → r,
      and.intro
        (assume hp : p, h (or.inl hp))
        (assume hq : q, h (or.inr hq)))
    (assume h : (p → r) ∧ (q → r),
      and.elim h
        (assume pr : p → r, assume qr : q → r,
          assume pq : p ∨ q, or.elim pq pr qr))

-- Below is just a special case of the above theorem but I'm not sure
-- how to express it:
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  iff.intro
    (assume h : ¬(p ∨ q),
      and.intro
        (assume hp : p, h (or.inl hp))
        (assume hq : q, h (or.inr hq)))
    (assume h : ¬p ∧ ¬q,
      and.elim h
        (assume np : ¬p, assume nq : ¬q,
          not.intro
            (assume pq : p ∨ q, or.elim pq np nq)))

theorem dm1 : ¬p ∨ ¬q → ¬(p ∧ q) :=
  assume npq : ¬p ∨ ¬q,
    or.elim npq
      (assume np : ¬p,
        not.intro
          (assume pq : p ∧ q, np (and.elim_left pq)))
      (assume nq : ¬q,
        not.intro
          (assume pq : p ∧ q, nq (and.elim_right pq)))

example : ¬(p ∧ ¬ p) :=
  assume pnp : p ∧ ¬p,
    and.elim pnp (assume hp : p, assume hnp : ¬p, hnp hp)

example : p ∧ ¬q → ¬(p → q) :=
  assume pnq : p ∧ ¬q,
    not.intro (assume pq : p → q,
      and.elim pnq (assume hp : p, assume hnq : ¬q,
        hnq (pq hp)))

example : ¬p → (p → q) :=
  assume hnp : ¬p, assume hp : p, absurd hp hnp

example : (¬p ∨ q) → (p → q) :=
  assume npq : ¬p ∨ q, assume hp : p,
    or.elim npq
      (assume hnp : ¬p, absurd hp hnp)
      (assume hq : q, hq)

example : p ∨ false ↔ p :=
  iff.intro
    (assume pf : p ∨ false,
      or.elim pf (assume hp : p, hp) false.elim)
    (assume hp : p, or.inl hp)

example : p ∧ false ↔ false :=
  iff.intro (assume pf : p ∧ false, and.right pf) false.elim

theorem thm1 : (p → ¬p) → ¬p :=
  assume h : p → ¬p,
  assume h2 : p,
  (h h2) h2

-- "If (p → ¬p), then (p → (p → false)), so in particular (p →
-- false). Put another way, (p → ¬p) → ¬p is an intuitionistically
-- valid theorem. From this, you have ¬p and ¬p → p from the
-- assumptions, so p, so false."

example : ¬(p ↔ ¬p) :=
  not.intro
    (assume impl : p ↔ ¬p,
     have hnp : ¬p, from thm1 p (iff.mp impl),
     have hp : p, from (iff.mpr impl) hnp,
     hnp hp)

theorem cp : (p → q) → (¬q → ¬p) :=
  assume pq : p → q,
  assume nq : ¬q,
  show p → false, from
    assume hp : p, nq (pq hp)

-- these require classical reasoning
example : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
  assume rps : p → r ∨ s,
  by_cases
    (assume hp : p,
      or.elim (rps hp)
        (assume hr : r, or.inl (assume hp2 : p, hr))
        (assume hs : s, or.inr (assume hp2 : p, hs)))
    (assume hnp : ¬p,
      or.inl (assume hp : p, absurd hp hnp))

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  assume npq : ¬(p ∧ q),
  by_cases
    (assume hp : p,
      by_cases
        (assume hq : q,
          have pq : p ∧ q, from and.intro hp hq,
          absurd pq npq)
        (assume hnq : ¬q, or.inr hnq))
    (assume hnp : ¬p, or.inl hnp)
  
example : ¬(p → q) → p ∧ ¬q :=
  assume npq : ¬(p → q),
  by_cases
    (assume hq : q, absurd (assume p, hq) npq)
    (assume hnq : ¬q,
      by_cases
        (assume hp : p, and.intro hp hnq)
        (assume hnp : ¬p,
          have pq : p → q, from (assume hp : p, absurd hp hnp),
          absurd pq npq))

example : (p → q) → (¬p ∨ q) :=
  assume pq : p → q, by_cases
    (assume hp : p, or.inr (pq hp))
    (assume hnp : ¬p, or.inl hnp)

theorem dne {p : Prop} (h : ¬¬p) : p :=
or.elim (em p)
  (assume hp : p, hp)
  (assume hnp : ¬p, absurd hnp h)

-- How is this so simple?
theorem dne2 {p : Prop} (hp : p) : ¬¬p :=
  (assume hnp : ¬p, hnp hp)

theorem cp2 : (¬q → ¬p) → (p → q) :=
  assume npnq : ¬q → ¬p,
  have pq2 : ¬¬p → ¬¬q, from cp (¬q) (¬p) npnq,
  assume hp : p, dne (pq2 (dne2 hp))

-- Is this cheating?
example : p ∨ ¬p := em p

example : (((p → q) → p) → p) :=
  assume pqp : ((p → q) → p),
  by_cases
    (assume hq : q,
      have pq : p → q, from (assume p, hq), pqp pq)
    (assume hnq : ¬q,
      by_cases
        (assume hp : p, hp)
        (assume hnp : ¬p,
          have pq : p → q, from cp2 p q (assume hnq : ¬q, hnp),
          have hp : p, from pqp pq,
          absurd hp hnp))
  -- Is there a simpler way to show the above?  Maybe proof by
  -- contradiction or something?
