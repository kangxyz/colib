/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectSupportedApproximation
public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedOpenFibration
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.CoarseJoint

/-!
# Supported bounded-flat complexes with open-detected weak equivalences

The objects, admissible supported quotients and chosen zero are unchanged. Only weakness
is enlarged, by actual restriction along the localization open. Fine approximation retains
its actual intermediate complex and quotient in this relative comparison.

Adapted from Quillen `BoundedFlat/SupportedOpenComparison.lean:36-75` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The target is the original relative category
on the ambient scheme, not all supported perfect complexes on the open.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.Fibration

universe u
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- Keep the supported bounded-flat exact category, detecting weak maps on the open. -/
def boundedAboveFlatPerfectSupportedOpenWaldhausen :
    Waldhausen.Structure (boundedAboveFlatPerfectSupported T.ι).FullSubcategory :=
  Structure.withInverseImageWeak
    ((boundedAboveFlatPerfectSupportedInclusion_isExact T.ι).comp
      (perfectSupportedRestrict_exact j T))

/-- Actual quasi-isomorphisms are included in the open-detected weak class. -/
def boundedAboveFlatPerfectSupportedOpenNested :
    NestedWeakEquivalences (boundedAboveFlatPerfectSupportedWaldhausen T.ι) :=
  Structure.inverseImageWeakNested
    ((boundedAboveFlatPerfectSupportedInclusion_isExact T.ι).comp
      (perfectSupportedRestrict_exact j T))

/-- Relative weakness tests the actual restricted underlying chain map. -/
theorem boundedAboveFlatPerfectSupportedOpenWaldhausen_weq_iff
    {K L : (boundedAboveFlatPerfectSupported T.ι).FullSubcategory} (f : K ⟶ L) :
    (boundedAboveFlatPerfectSupportedOpenWaldhausen j T).weq f ↔
      QuasiIso (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map f.hom) :=
  Iff.rfl

/-- The relative model keeps exactly the original admissible supported quotients. -/
theorem boundedAboveFlatPerfectSupportedOpenWaldhausen_cof_iff
    {K L : (boundedAboveFlatPerfectSupported T.ι).FullSubcategory} (f : K ⟶ L) :
    (boundedAboveFlatPerfectSupportedOpenWaldhausen j T).cof f ↔
      ∃ (Q : CochainComplex X.Modules ℤ) (_hQ : boundedAboveFlatPerfectSupported T.ι Q)
        (p : L.obj ⟶ Q) (h : f.hom ≫ p = 0),
        (ShortComplex.mk f.hom p h).ShortExact :=
  boundedAboveFlatPerfectSupportedWaldhausen_cof_iff T.ι f

/-- The literal supported inclusion is exact for the two actual relative weak classes. -/
theorem boundedAboveFlatPerfectSupportedOpenInclusion_isExact :
    IsExact (boundedAboveFlatPerfectSupportedOpenWaldhausen j T).cof
      (boundedAboveFlatPerfectSupportedOpenWaldhausen j T).weq
      (perfectSupportedOpenWeakWaldhausen j T).cof
      (perfectSupportedOpenWeakWaldhausen j T).weq
      (boundedAboveFlatPerfectSupportedInclusion T.ι) where
  zero := (boundedAboveFlatPerfectSupportedInclusion_isExact T.ι).zero
  cofibration := (boundedAboveFlatPerfectSupportedInclusion_isExact T.ι).cofibration
  weak _ h := h
  pushout := (boundedAboveFlatPerfectSupportedInclusion_isExact T.ι).pushout

/-- The actual identity-cone joint cylinder retains both endpoints and its projection. -/
def boundedAboveFlatPerfectSupportedOpenJointData :
    RowFactorization.JointData (boundedAboveFlatPerfectSupportedOpenNested j T) :=
  complexJointDataOfNested (boundedAboveFlatPerfectSupported T.ι)
    (fun hK hL f => boundedAboveFlatPerfectSupported_mappingCone T.ι hK hL f)
    (fun _ hK => boundedAboveFlatPerfectSupported_shift_one T.ι hK)
    (boundedAboveFlatPerfectSupportedOpenNested j T)

/-- Fine supported replacements give actual relative approximation. Only the ambient
scheme needs compact underlying space, with no compactness condition on either open. -/
@[colib_tag "COL-0383",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedOpenComparison.lean:68-75"
    "adaptation" "Actual relative App2 from supported fine replacement on a compact ambient scheme"]
theorem boundedAboveFlatPerfectSupportedOpenInclusion_approximation [CompactSpace X] :
    HasApproximationProperty (boundedAboveFlatPerfectSupportedOpenWaldhausen j T)
      (perfectSupportedOpenWeakWaldhausen j T) (boundedAboveFlatPerfectSupportedInclusion T.ι) where
  reflects _ h := h
  lift f := by
    obtain ⟨M, i, p, hi, hp, hfac⟩ :=
      (boundedAboveFlatPerfectSupportedInclusion_approximation T.ι).lift f
    exact ⟨M, i, p, hi, (perfectSupportedOpenNested j T).le_weq p hp, hfac⟩

instance boundedAboveFlatPerfectSupportedOpenNested_twoOutOfThree :
    (boundedAboveFlatPerfectSupportedOpenNested j T).coarse.weq.HasTwoOutOfThreeProperty := by
  let : (complexes U.Modules).weq.HasTwoOutOfThreeProperty := by
    change (HomologicalComplex.quasiIso U.Modules (ComplexShape.up ℤ)).HasTwoOutOfThreeProperty
    infer_instance
  let : (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).weq.HasTwoOutOfThreeProperty :=
    CofibrationClosedSubcategory.twoOutOfThree _ _ _
  exact Structure.withInverseImageWeak_twoOutOfThree
    ((boundedAboveFlatPerfectSupportedInclusion_isExact T.ι).comp
      (perfectSupportedRestrict_exact j T))

end AlgebraicGeometry.Scheme.Modules
