import AcyclicCompletion.Obstructions

namespace AcyclicCompletion

structure ProperNineColoring {V : Type}
    (c : V → V → Nat) : Prop where
  symmetric : ∀ u v, c u v = c v u
  diagonal : ∀ u, c u u = 0
  palette : ∀ u v, u ≠ v → 1 ≤ c u v ∧ c u v ≤ 9
  proper : ∀ u v w,
    u ≠ v → u ≠ w → v ≠ w → c u v ≠ c u w

theorem witness_is_proper : ProperNineColoring color where
  symmetric := color_symmetric
  diagonal := color_diagonal
  palette := color_palette
  proper := color_proper

theorem no_completion
    (c : Option (Fin 8) → Option (Fin 8) → Nat)
    (hc : ProperNineColoring c)
    (hkeep : ∀ u v : Fin 8,
      c (some u) (some v) = color u v) :
    ¬ IsAcyclic c := by
  let f : Fin 8 → Nat := fun u => c none (some u)
  have hp : ∀ u, 1 ≤ f u ∧ f u ≤ 9 := by
    intro u
    exact hc.palette none (some u) (by simp)
  have hi : ∀ u v, u ≠ v → f u ≠ f v := by
    intro u v huv
    exact hc.proper none (some u) (some v)
      (by simp) (by simp)
      (by
        intro h
        exact huv (Option.some.inj h))
  have hl : ∀ u v, u ≠ v → f u ≠ color u v := by
    intro u v huv
    have h := hc.proper (some u) none (some v)
      (by simp)
      (by
        intro h
        exact huv (Option.some.inj h))
      (by simp)
    rw [hc.symmetric (some u) none, hkeep u v] at h
    exact h
  have heq : c = extendedColor f := by
    funext u v
    cases u with
    | none =>
        cases v with
        | none => exact hc.diagonal none
        | some v => rfl
    | some u =>
        cases v with
        | none => exact hc.symmetric (some u) none
        | some v => exact hkeep u v
  rw [heq]
  exact no_acyclic_extension_star f hp hi hl

theorem certified_counterexample :
    ProperNineColoring color ∧
    IsAcyclic color ∧
    ¬ (∃ c : Option (Fin 8) → Option (Fin 8) → Nat,
      ProperNineColoring c ∧
      (∀ u v : Fin 8, c (some u) (some v) = color u v) ∧
      IsAcyclic c) := by
  refine ⟨witness_is_proper, color_acyclic, ?_⟩
  intro h
  obtain ⟨c, hc, hkeep, ha⟩ := h
  exact no_completion c hc hkeep ha

#print axioms certified_counterexample

end AcyclicCompletion
