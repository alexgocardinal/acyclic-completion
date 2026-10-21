import AcyclicCompletion.Extension

namespace AcyclicCompletion

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def extendedColor (f : Fin 8 → Nat) :
    Option (Fin 8) → Option (Fin 8) → Nat
  | none, none => 0
  | none, some v => f v
  | some u, none => f u
  | some u, some v => color u v

def cyclicNext {n : Nat} (i : Fin (n + 1)) :
    Fin (n + 1) :=
  ⟨(i.val + 1) % (n + 1), Nat.mod_lt _ (by omega)⟩

def cyclicPrev {n : Nat} (i : Fin (n + 1)) :
    Fin (n + 1) :=
  ⟨(i.val + n) % (n + 1), Nat.mod_lt _ (by omega)⟩

-- The cycle x-0-4-5-6-2-x.
def sixVertices (i : Fin 6) : Option (Fin 8) :=
  ([none, some 0, some 4, some 5, some 6, some 2] :
    List (Option (Fin 8))).getD i.val none

def obstructionSix
    (f : Fin 8 → Nat) (h0 : f 0 = 2) (h2 : f 2 = 4) :
    TwoColorCycle (extendedColor f) 2 4 where
  size := 5
  vertex := sixVertices
  vertex_injective := by decide
  next := cyclicNext
  prev := cyclicPrev
  next_prev := by decide
  prev_next := by decide
  next_ne_self := by decide
  neighbors_distinct := by decide
  edge_colors := by
    intro i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨
        i = 3 ∨ i = 4 ∨ i = 5 := by
      have all : ∀ j : Fin 6,
          j = 0 ∨ j = 1 ∨ j = 2 ∨
          j = 3 ∨ j = 4 ∨ j = 5 := by decide
      exact all i
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · change f 0 = 2 ∨ f 0 = 4
      exact Or.inl h0
    · change 4 = 2 ∨ 4 = 4
      decide
    · change 2 = 2 ∨ 2 = 4
      decide
    · change 4 = 2 ∨ 4 = 4
      decide
    · change 2 = 2 ∨ 2 = 4
      decide
    · change f 2 = 2 ∨ f 2 = 4
      exact Or.inr h2

-- The cycle x-1-7-3-x.
def fourVertices (i : Fin 4) : Option (Fin 8) :=
  ([none, some 1, some 7, some 3] :
    List (Option (Fin 8))).getD i.val none

def obstructionFour
    (f : Fin 8 → Nat) (h1 : f 1 = 2) (h3 : f 3 = 4) :
    TwoColorCycle (extendedColor f) 2 4 where
  size := 3
  vertex := fourVertices
  vertex_injective := by decide
  next := cyclicNext
  prev := cyclicPrev
  next_prev := by decide
  prev_next := by decide
  next_ne_self := by decide
  neighbors_distinct := by decide
  edge_colors := by
    intro i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
      have all : ∀ j : Fin 4,
          j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide
      exact all i
    rcases hi with rfl | rfl | rfl | rfl
    · change f 1 = 2 ∨ f 1 = 4
      exact Or.inl h1
    · change 4 = 2 ∨ 4 = 4
      decide
    · change 2 = 2 ∨ 2 = 4
      decide
    · change f 3 = 2 ∨ f 3 = 4
      exact Or.inr h3

theorem no_acyclic_extension_star
    (f : Fin 8 → Nat)
    (hpalette : ∀ u, 1 ≤ f u ∧ f u ≤ 9)
    (hinjective : ∀ u v, u ≠ v → f u ≠ f v)
    (hlocal : ∀ u v, u ≠ v → f u ≠ color u v) :
    ¬ IsAcyclic (extendedColor f) := by
  intro hac
  have hforbid := hac (1 : Fin 9) (3 : Fin 9) (by decide)
  rcases extension_forces_obstruction
      f hpalette hinjective hlocal with h | h
  · exact hforbid ⟨obstructionSix f h.1 h.2⟩
  · exact hforbid ⟨obstructionFour f h.1 h.2⟩

end AcyclicCompletion
