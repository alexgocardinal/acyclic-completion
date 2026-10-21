import AcyclicCompletion.NoCycle

namespace AcyclicCompletion

structure TwoColorCycle {V : Type}
    (c : V → V → Nat) (a b : Nat) where
  size : Nat
  vertex : Fin (size + 1) → V
  vertex_injective :
    ∀ i j, vertex i = vertex j → i = j
  next : Fin (size + 1) → Fin (size + 1)
  prev : Fin (size + 1) → Fin (size + 1)
  next_prev : ∀ i, next (prev i) = i
  prev_next : ∀ i, prev (next i) = i
  next_ne_self : ∀ i, next i ≠ i
  neighbors_distinct : ∀ i, next i ≠ prev i
  edge_colors : ∀ i,
    c (vertex i) (vertex (next i)) = a ∨
    c (vertex i) (vertex (next i)) = b

def IsAcyclic {V : Type} (c : V → V → Nat) : Prop :=
  ∀ a b : Fin 9, a ≠ b →
    ¬ Nonempty (TwoColorCycle c (a.val + 1) (b.val + 1))

theorem no_cycle_from_embedding
    {V : Type} (c : V → V → Nat)
    (a b : Nat) (p : V → Nat)
    (hinjective : ∀ u v, p u = p v → u = v)
    (hedges : ∀ u v, (c u v = a ∨ c u v = b) →
      p u + 1 = p v ∨ p v + 1 = p u) :
    ¬ Nonempty (TwoColorCycle c a b) := by
  intro h
  obtain ⟨C⟩ := h
  apply no_cycle_of_positions C.size
    (fun i => p (C.vertex i)) C.next C.prev
  · intro i j hij
    exact C.vertex_injective i j
      (hinjective _ _ hij)
  · exact C.next_prev
  · exact C.neighbors_distinct
  · intro i
    exact hedges _ _ (C.edge_colors i)

theorem color_acyclic : IsAcyclic color := by
  intro a b hab
  by_cases hlt : a.val < b.val
  · obtain ⟨hinj, hedges⟩ := pair_path_certificates a b hlt
    exact no_cycle_from_embedding color
      (a.val + 1) (b.val + 1)
      (position (a.val + 1) (b.val + 1))
      hinj hedges
  · have hne : a.val ≠ b.val := by
      intro h
      exact hab (Fin.ext h)
    have hgt : b.val < a.val := by omega
    obtain ⟨hinj, hedges⟩ := pair_path_certificates b a hgt
    apply no_cycle_from_embedding color
      (a.val + 1) (b.val + 1)
      (position (b.val + 1) (a.val + 1)) hinj
    intro u v h
    exact hedges u v h.symm

end AcyclicCompletion
