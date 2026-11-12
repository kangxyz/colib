/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.AmpleTwistingSheaf
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothProjectiveVariety
/-! # The actual ample coefficient of a finite projective presentation -/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Stacks.Ample Stacks.AmpleProjectiveImmersion
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

variable (R : Type u) [CommRing R] (n : ℕ) {C : Scheme.{u}}
  (f : C ⟶ projectiveSpaceOverRing n (.of R)) [IsFinite f]

/-- The literal pullback of the native hyperplane module, with no supplied line. -/
def finiteProjectiveCoefficient : C.Modules :=
  (Modules.pullback f).obj (projectiveSpaceTwistingSheaf n (Spec (.of R)))

instance : IsInvertibleModule C (finiteProjectiveCoefficient R n f) :=
  Stacks.InvertiblePullback.isInvertibleModule_pullback f _

/-- Affineness of a finite map pulls native O(1) ampleness back over any ring. -/
theorem finiteProjectiveCoefficient_isAmple :
    IsAmple C (finiteProjectiveCoefficient R n f) :=
  Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom f _
    (Stacks.ProjectiveSpace.isAmple_projectiveSpaceTwistingSheaf n (Spec (.of R)))

/-- The actual compactification projection is proper over its affine base. -/
instance : IsProper (f ≫ (projectiveSpaceOverRing n (.of R) ↘ Spec (.of R))) := by
  infer_instance

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
