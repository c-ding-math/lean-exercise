open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  λ h => Or.elim (Classical.em q)
    (λ hq => Or.inl (λ _ => hq))
    (λ hnq => Or.inr (λ hp => Or.resolve_left (h hp) hnq))

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  fun h => Or.elim (Classical.em p)
    (λ hp => Or.inr (λ hq => h ⟨hp, hq⟩))
    (λ hnp => Or.inl hnp)

example : ¬(p → q) → p ∧ ¬q :=
  fun h => Or.elim (Classical.em p)
    (λ hp => Or.elim (Classical.em q)
      (λ hq => False.elim (h (λ _ => hq)))
      (λ hnq => ⟨hp, hnq⟩))
    (λ hnp => False.elim (h (λ hp => absurd hp hnp)))

example : (p → q) → (¬p ∨ q) :=
  fun h => Or.elim (Classical.em p)
    (λ hp => Or.inr (h hp))
    (λ hnp => Or.inl hnp)

example : (¬q → ¬p) → (p → q) :=
  fun h => Or.elim (Classical.em p)
    (λ hp => Or.elim (Classical.em q)
      (λ hq => λ _ => hq)
      (λ hnq => False.elim (h hnq hp)))
    (λ hnp => λ hp => False.elim (hnp hp))

example : p ∨ ¬p := em p

example : (((p → q) → p) → p) :=
  fun h => Or.elim (Classical.em p)
    (λ hp => hp)
    (λ hnp => absurd (h (λ hp => absurd hp hnp)) hnp)
