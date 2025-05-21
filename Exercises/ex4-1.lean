variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
    (fun h => ⟨fun x => (h x).left, fun x => (h x).right⟩)
    (fun ⟨hp, hq⟩ x => ⟨hp x, hq x⟩)
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun hpq hp x => hpq x (hp x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun h x => Or.elim h (fun hp => Or.inl (hp x)) (fun hq => Or.inr (hq x))
