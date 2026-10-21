import AcyclicCompletion.Forest

namespace AcyclicCompletion

theorem no_cycle_of_positions
    (n : Nat)
    (r : Fin (n + 1) → Nat)
    (next prev : Fin (n + 1) → Fin (n + 1))
    (hinjective : ∀ i j, r i = r j → i = j)
    (hinverse : ∀ i, next (prev i) = i)
    (hdistinct : ∀ i, next i ≠ prev i)
    (hstep : ∀ i,
      r i + 1 = r (next i) ∨
      r (next i) + 1 = r i) :
    False := by
  obtain ⟨i, hi⟩ := finite_maximum n r
  have hn := hstep i
  have hp := hstep (prev i)
  rw [hinverse i] at hp
  have hnle := hi (next i)
  have hple := hi (prev i)
  have heq : r (next i) = r (prev i) := by
    omega
  exact hdistinct i (hinjective _ _ heq)

end AcyclicCompletion
