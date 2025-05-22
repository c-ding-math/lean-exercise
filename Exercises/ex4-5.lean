open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r :=
  fun ⟨_, hr⟩ => hr
example (a : α) : r → (∃ x : α, r) :=
  fun hr => ⟨a, hr⟩
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
    (fun ⟨x, ⟨hp, hr⟩⟩ => ⟨⟨x, hp⟩, hr⟩)
    (fun ⟨⟨x, hp⟩, hr⟩ => ⟨x, ⟨hp, hr⟩⟩)
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (fun |⟨x, Or.inl hp⟩ => Or.inl ⟨x, hp⟩ | ⟨x, Or.inr hq⟩ => Or.inr ⟨x, hq⟩)
    (fun | Or.inl ⟨x, hp⟩ => ⟨x, Or.inl hp⟩ | Or.inr ⟨x, hq⟩ => ⟨x, Or.inr hq⟩)

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := Iff.intro
  (fun h => fun ⟨x, hnpx⟩ => hnpx (h x))
  (fun h x => Or.elim (Classical.em (p x))
    (fun hp => hp)
    (fun hnp => False.elim (h ⟨x, hnp⟩)))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := Iff.intro
  (fun ⟨x, hp⟩ => fun h => (h x hp))
  (fun h : ¬ (∀ x, ¬ p x) => byContradiction fun h1 : ¬ (∃ x, p x) =>
    h (fun hx hpx => h1 ⟨hx, hpx⟩))

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
