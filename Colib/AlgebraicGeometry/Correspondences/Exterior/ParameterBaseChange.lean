/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.ParameterMap

/-!
# Parameter maps are actual Cartesian base changes

The actual support map is a base change of the parameter morphism, not merely a
map with commuting projections. Native base-change stability therefore supplies
flatness, finiteness and closed immersions when the parameter map has that
property. This is geometric preparation for cycle comparison, not a Tor or
multiplicity comparison theorem.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
universe u
namespace Stacks.Chow
variable {S : Scheme.{u}} (X Y : SmoothSite S)
  (W : (pullback X.hom Y.hom).IdealSheafData) {T U : SmoothSite S} (ψ : T ⟶ U)

/-- The parameter-map square of the actual exterior support is Cartesian. -/
theorem exteriorParameterMap_isPullback :
    IsPullback (exteriorParameterMap X Y W ψ)
      (pullback.snd (exteriorSupportSourceProjection X Y W ≫ X.hom) T.hom)
      (pullback.snd (exteriorSupportSourceProjection X Y W ≫ X.hom) U.hom) ψ.left := by
  refine IsPullback.of_right ?_ (exteriorParameterMap_snd X Y W ψ)
    (IsPullback.of_hasPullback (exteriorSupportSourceProjection X Y W ≫ X.hom) U.hom)
  simpa only [exteriorParameterMap_fst, MorphismProperty.Over.w] using
    (IsPullback.of_hasPullback (exteriorSupportSourceProjection X Y W ≫ X.hom) T.hom)

instance exteriorParameterMap_flat [Flat ψ.left] : Flat (exteriorParameterMap X Y W ψ) :=
  MorphismProperty.of_isPullback (exteriorParameterMap_isPullback X Y W ψ).flip inferInstance

instance exteriorParameterMap_isFinite [IsFinite ψ.left] :
    IsFinite (exteriorParameterMap X Y W ψ) :=
  MorphismProperty.of_isPullback (exteriorParameterMap_isPullback X Y W ψ).flip inferInstance

instance exteriorParameterMap_isClosedImmersion [IsClosedImmersion ψ.left] :
    IsClosedImmersion (exteriorParameterMap X Y W ψ) :=
  MorphismProperty.of_isPullback (exteriorParameterMap_isPullback X Y W ψ).flip inferInstance

attribute [colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Simplex/GraphInterchangeIncidence.lean:34-49"
  "ingredient"
    "The original parameter map and its two projections; Cartesianity is proved natively"]
  exteriorParameterMap_isPullback

attribute [colib_ref "mathlib_stable_localization_pin"
  "Mathlib/CategoryTheory/Limits/Shapes/Pullback/IsPullback/Basic.lean:229-234"
  "specialization" "Pullback cancellation proves the actual parameter-map square is Cartesian"]
  exteriorParameterMap_isPullback

attribute [colib_ref "mathlib_stable_localization_pin"
  "Mathlib/CategoryTheory/MorphismProperty/Limits.lean:105-109,162"
  "specialization" "Native base-change stability on the actual parameter-map pullback square"]
  exteriorParameterMap_flat
  exteriorParameterMap_isFinite
  exteriorParameterMap_isClosedImmersion

end Stacks.Chow
