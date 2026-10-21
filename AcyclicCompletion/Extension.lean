import AcyclicCompletion.Acyclic

namespace AcyclicCompletion

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def missingFirst (u : Fin 8) : Nat :=
  ([2,2,3,4,5,6,7,8] : List Nat).getD u.val 0

def missingSecond (u : Fin 8) : Nat :=
  ([9,3,4,5,6,7,8,9] : List Nat).getD u.val 0

theorem missing_color_certificate :
    ∀ u : Fin 8, ∀ k : Fin 10, 1 ≤ k.val →
      (∀ v : Fin 8, u ≠ v → k.val ≠ color u v) →
      k.val = missingFirst u ∨
      k.val = missingSecond u := by
  decide

theorem extension_forces_obstruction
    (f : Fin 8 → Nat)
    (hpalette : ∀ u, 1 ≤ f u ∧ f u ≤ 9)
    (hinjective : ∀ u v, u ≠ v → f u ≠ f v)
    (hlocal : ∀ u v, u ≠ v → f u ≠ color u v) :
    (f 0 = 2 ∧ f 2 = 4) ∨
    (f 1 = 2 ∧ f 3 = 4) := by
  have hm (u : Fin 8) :
      f u = missingFirst u ∨ f u = missingSecond u := by
    exact missing_color_certificate u
      ⟨f u, by have hp := hpalette u; omega⟩
      (hpalette u).1 (hlocal u)
  have h0 := hm 0
  have h1 := hm 1
  have h2 := hm 2
  have h3 := hm 3
  have h4 := hm 4
  have h5 := hm 5
  have h6 := hm 6
  have h7 := hm 7
  change f 0 = 2 ∨ f 0 = 9 at h0
  change f 1 = 2 ∨ f 1 = 3 at h1
  change f 2 = 3 ∨ f 2 = 4 at h2
  change f 3 = 4 ∨ f 3 = 5 at h3
  change f 4 = 5 ∨ f 4 = 6 at h4
  change f 5 = 6 ∨ f 5 = 7 at h5
  change f 6 = 7 ∨ f 6 = 8 at h6
  change f 7 = 8 ∨ f 7 = 9 at h7
  have h01 := hinjective 0 1 (by decide)
  have h12 := hinjective 1 2 (by decide)
  have h23 := hinjective 2 3 (by decide)
  have h34 := hinjective 3 4 (by decide)
  have h45 := hinjective 4 5 (by decide)
  have h56 := hinjective 5 6 (by decide)
  have h67 := hinjective 6 7 (by decide)
  have h70 := hinjective 7 0 (by decide)
  omega

end AcyclicCompletion
