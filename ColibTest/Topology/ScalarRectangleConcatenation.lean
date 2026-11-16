import Colib.Topology.Path.ScalarRectangleConcatenation

open Topology Topology.ScalarRectangle
open scoped Topology unitInterval

universe u

/-- The last original cell reverses only the overlap clock, before any evaluation. -/
example {X : Type u} [TopologicalSpace X]
    (P A B M : C(unitInterval × unitInterval, X))
    (hBM : ∀ s, B (s, 1) = (⟨fun w ↦ M (w.1, unitInterval.symm w.2),
      by fun_prop⟩ : C(unitInterval × unitInterval, X)) (s, 0))
    (hA : ∀ s, A (s, 1) = concatSecond B _ hBM (s, 0))
    (h₁ : ∀ t, P (1, firstHalfTime t) = A (0, t))
    (h₂ : ∀ t, P (1, secondHalfTime (firstHalfTime t)) = B (0, t))
    (h₃ : ∀ t, P (1, secondHalfTime (secondHalfTime t)) = M (0, unitInterval.symm t))
    (s t : unitInterval) :
    concatFirst P (concatSecond A (concatSecond B _ hBM) hA)
        (rightAssociated_seam hBM hA h₁ h₂ h₃)
        (secondHalfTime s, secondHalfTime (secondHalfTime t)) =
      M (s, unitInterval.symm t) := by
  rw [concatFirst_upper, concatSecond_upper, concatSecond_upper] <;> rfl
