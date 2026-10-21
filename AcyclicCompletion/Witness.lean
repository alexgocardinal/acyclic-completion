import Std

namespace AcyclicCompletion

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def matrix : List (List Nat) := [
  [0,7,8,6,4,3,1,5],
  [7,0,6,1,8,9,5,4],
  [8,6,0,9,1,5,2,7],
  [6,1,9,0,7,8,3,2],
  [4,8,1,7,0,2,9,3],
  [3,9,5,8,2,0,4,1],
  [1,5,2,3,9,4,0,6],
  [5,4,7,2,3,1,6,0]
]

def color (u v : Fin 8) : Nat :=
  (matrix.getD u.val []).getD v.val 0

theorem color_symmetric :
    ∀ u v : Fin 8, color u v = color v u := by
  decide

theorem color_diagonal :
    ∀ u : Fin 8, color u u = 0 := by
  decide

theorem color_palette :
    ∀ u v : Fin 8, u ≠ v →
      1 ≤ color u v ∧ color u v ≤ 9 := by
  decide

theorem color_proper :
    ∀ u v w : Fin 8,
      u ≠ v → u ≠ w → v ≠ w →
      color u v ≠ color u w := by
  decide

end AcyclicCompletion
