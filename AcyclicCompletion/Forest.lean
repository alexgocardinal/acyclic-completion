import AcyclicCompletion.Paths

namespace AcyclicCompletion

theorem finite_maximum (n : Nat) (f : Fin (n + 1) → Nat) :
    ∃ i, ∀ j, f j ≤ f i := by
  induction n with
  | zero =>
      refine ⟨0, ?_⟩
      intro j
      have hj : j = 0 := by
        apply Fin.ext
        omega
      simp [hj]
  | succ n ih =>
      obtain ⟨i, hi⟩ := ih (fun j => f j.succ)
      by_cases h : f 0 ≤ f i.succ
      · refine ⟨i.succ, ?_⟩
        intro j
        exact Fin.cases h (fun k => hi k) j
      · refine ⟨0, ?_⟩
        intro j
        refine Fin.cases (Nat.le_refl _) (fun k => ?_) j
        have hk := hi k
        omega

end AcyclicCompletion
