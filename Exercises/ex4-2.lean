variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) :=
  fun x => Iff.intro (fun hr  => hr x) (fun hr _ => hr)

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
    (fun h => Or.elim (Classical.em r)
      (fun hr => Or.inr hr)
      (fun hnr => Or.inl (fun x => Or.resolve_right (h x) hnr)))
    (fun h x => Or.elim h (fun hp => Or.inl (hp x)) (fun hr => Or.inr hr))
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
    (fun h hr x => h x hr)
    (fun h x hr => h hr x)
