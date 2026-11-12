/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothProjectiveVariety
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.Normal

/-!
# The relative projective line on an affine parameter

The literal pullback of the relative projective line to an integral affine
parameter is integral. Normality and Noetherianity follow from the same
base-changed smooth projective projection.

Adapted from
`Motivic/Aglib/AlgebraicGeometry/ProjectiveLine/Neighborhood/Source/AffineParameterNormal.lean`
at a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The projective line over the actual integral affine parameter is integral. -/
theorem isIntegral_pullback_projectiveLine {S X : Scheme.{u}} [IsAffine X] [IsIntegral X]
    (f : X ⟶ S) : IsIntegral (pullback f (projectiveSpaceOver 1 S ↘ S)) := by
  let : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.choice inferInstance, trivial⟩⟩
  let : IsDomain Γ(X, ⊤) := IsIntegral.component_integral (⊤ : X.Opens)
  let : IsIntegral (projectiveSpaceOver 1 (Spec Γ(X, ⊤))) :=
    inferInstanceAs (IsIntegral (projectiveSpaceOverRing 1 (.of Γ(X, ⊤))))
  let g := projectiveSpaceOverMap 1 X.isoSpec.inv
  let : IsIso g := (isPullback_projectiveSpaceOverMap 1 X.isoSpec.inv).isIso_fst_of_isIso
  let : IsIntegral (projectiveSpaceOver 1 X) := IsIntegral.of_isIso g
  let e : projectiveSpaceOver 1 X ≅ pullback f (projectiveSpaceOver 1 S ↘ S) :=
    (isPullback_projectiveSpaceOverMap 1 f).flip.isoPullback
  exact IsIntegral.of_isIso e.hom

/-- The same affine parameter product is normal and Noetherian. -/
theorem isNormal_isNoetherian_pullback_projectiveLine {S X : Scheme.{u}}
    [IsAffine X] [IsNormal X] [IsLocallyNoetherian X] (f : X ⟶ S) :
    IsNormal (pullback f (projectiveSpaceOver 1 S ↘ S)) ∧
      IsNoetherian (pullback f (projectiveSpaceOver 1 S ↘ S)) := by
  let p := pullback.fst f (projectiveSpaceOver 1 S ↘ S)
  let : IsLocallyNoetherian (pullback f (projectiveSpaceOver 1 S ↘ S)) :=
    LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace (pullback f (projectiveSpaceOver 1 S ↘ S) : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace p
  exact ⟨isNormal_of_smooth p, {
    toIsLocallyNoetherian := inferInstance
    toCompactSpace := inferInstance }⟩

end AlgebraicGeometry
