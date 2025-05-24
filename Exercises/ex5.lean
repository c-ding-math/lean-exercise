example (p q r : Prop) (hp : p)
  : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
        apply And.intro
        apply Or.inl
        exact hp
        apply And.intro
        apply Or.inr
        apply Or.inl
        exact hp
        apply Or.inr
        apply Or.inr
        exact hp
