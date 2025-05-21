variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  let h_barber := h barber
  (Classical.em (shaves barber barber)).elim
    (λ h_shaves => h_barber.mp h_shaves h_shaves)
    (λ h_not_shaves => h_not_shaves (h_barber.mpr h_not_shaves))
