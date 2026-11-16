module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedRawBassStep

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS Scheme.Modules.SupportedRawBass
open scoped Topology unitInterval

universe u

namespace ColibTest.SupportedRawBassStep

variable (A : Scheme.QuasiCompactOpenPairs.{u}) (n : ℕ)
  (x : (originalPrespectrum
    (Scheme.Modules.boundedAboveFlatPerfectSupportedWaldhausen A.obj.hom)).space n)

/-- At each time in the first half the actual positive composition track remains visible. -/
theorem source_null_positive_half (s : unitInterval) (hs : (s : ℝ) ≤ 1 / 2) :
    (sourceNull A).level n (s, x) =
      (mappingConeInclusion (comparison A)).map n
        ((plusHomotopy A).level n
          (⟨2 * s, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩, x)) := by
  rw [sourceNull_apply, dite_eq_left hs]

/-- The second half remains the original cone interval on the actual positive source leg. -/
theorem source_null_cone_half (s : unitInterval) (hs : ¬ (s : ℝ) ≤ 1 / 2) :
    (sourceNull A).level n (s, x) =
      (mappingConeHomotopy (comparison A)).level n
        (⟨2 * s - 1, unitInterval.two_mul_sub_one_mem_iff.2
          ⟨(not_le.1 hs).le, s.2.2⟩⟩, (sourceLeg A).map n x) := by
  rw [sourceNull_apply, dite_eq_right hs]

/-- Null and Laurent loop clocks are retained, not replaced by a stable homotopy class. -/
theorem transition_full_loop (s : unitInterval) :
    Path.toContinuousMap ((transition A).map n x) s =
      (((Scheme.Modules.boundedAboveFlatPerfectSupportedLaurentProjectionUnitHomotopy A).postcomp
        (mappingConeInclusion (comparison A))).conjugateToZero (sourceNull A)).level n (s, x) :=
  transition_apply A n x s

end ColibTest.SupportedRawBassStep
