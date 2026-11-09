/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.SupportedOpenDerivedImage.Exact
public import Colib.AlgebraicGeometry.Modules.PerfectSupportedJoint

/-!
# Actual native supported perfect complements and the honest restriction image

The geometric input states exactly that an actual native supported perfect complex on the open has
an actual native supported perfect complement whose sum is derived-isomorphic to a global supported
restriction.
It does not assume density, a K-equivalence or a cylinder. The coproduct comparison below
constructs density on the unchanged native supported perfect category from this precise input.
The geometric qcqs existence theorem is separate and is not asserted here.

Adapted from Quillen's `SupportedOpenDerivedImage/Complements.lean` and `GlobalComplements.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory

attribute [local instance] Abelian.hasFiniteBiproducts hasBinaryBiproducts_of_finite_biproducts

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme.Modules.SupportedOpenDerivedImage

universe u d

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)
  [HasDerivedCategory.{d} U.Modules]

/-- The exact outstanding geometric complement statement, in the chosen derived model. -/
def HasPerfectComplements : Prop :=
  ∀ (P : CochainComplex U.Modules ℤ),
    perfectSupported (j ⁻¹ᵁ T).ι P →
    ∃ (R : CochainComplex X.Modules ℤ) (C : CochainComplex U.Modules ℤ),
      perfectSupported T.ι R ∧
      perfectSupported (j ⁻¹ᵁ T).ι C ∧
      Nonempty (DerivedCategory.Q.obj
          (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj R) ≅
        DerivedCategory.Q.obj (P ⊞ C))

/-- The honest image predicate on the original native supported perfect category. -/
def objects : ObjectProperty
    (ObjectProperty.FullSubcategory (perfectSupported (j ⁻¹ᵁ T).ι)) :=
  fun A => complexObjects j T A.obj

/-- Native supported finite-product closure gives actual binary coproducts. -/
instance supportedComplexes_hasBinaryCoproducts :
    HasBinaryCoproducts (perfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory := by
  let : HasFiniteBiproducts (perfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory :=
    ExactSubcategory.subcategoryHasFiniteBiproducts (perfectSupported (j ⁻¹ᵁ T).ι)
  exact hasBinaryCoproducts_of_hasBinaryBiproducts

/-- An actual complex complement gives membership of the chosen categorical coproduct
through its genuine universal-property comparison, rather than definitional equality. -/
theorem coprod_complement_of_complex_complement
    (A : ObjectProperty.FullSubcategory (perfectSupported (j ⁻¹ᵁ T).ι))
    (C : CochainComplex U.Modules ℤ)
    (hC : perfectSupported (j ⁻¹ᵁ T).ι C)
    (hAC : complexObjects j T (A.obj ⊞ C)) :
    ∃ B, objects j T (A ⨿ B) := by
  let B : ObjectProperty.FullSubcategory
      (perfectSupported (j ⁻¹ᵁ T).ι) := ⟨C, hC⟩
  let S₀ : ObjectProperty.FullSubcategory
      (perfectSupported (j ⁻¹ᵁ T).ι) :=
    ⟨A.obj ⊞ B.obj, perfectSupported_X₂_of_shortExact (j ⁻¹ᵁ T).ι
      (ShortComplex.Splitting.ofHasBinaryBiproduct A.obj B.obj).shortExact
      A.property B.property⟩
  let il : A ⟶ S₀ := ObjectProperty.homMk biprod.inl
  let ir : B ⟶ S₀ := ObjectProperty.homMk biprod.inr
  have ht : IsColimit (BinaryCofan.mk il ir) := by
    refine BinaryCofan.IsColimit.mk _
      (fun f g => ObjectProperty.homMk (biprod.desc f.hom g.hom)) ?_ ?_ ?_
    · intro S f g
      apply ObjectProperty.hom_ext
      exact biprod.inl_desc _ _
    · intro S f g
      apply ObjectProperty.hom_ext
      exact biprod.inr_desc _ _
    · intro S f g m hm hn
      apply ObjectProperty.hom_ext
      apply biprod.hom_ext'
      · exact (congrArg (fun k => k.hom) hm).trans (biprod.inl_desc _ _).symm
      · exact (congrArg (fun k => k.hom) hn).trans (biprod.inr_desc _ _).symm
  let e : A ⨿ B ≅ S₀ := (coprodIsCoprod A B).coconePointUniqueUpToIso ht
  exact ⟨B, (complexObjects_iff_of_derivedIso j T
    (DerivedCategory.Q.mapIso
      ((ObjectProperty.ι (perfectSupported (j ⁻¹ᵁ T).ι)).mapIso e))).mpr
        hAC⟩

/-- The displayed geometric input constructs actual coproduct density. -/
theorem coprod_complement (hc : HasPerfectComplements j T)
    (A : ObjectProperty.FullSubcategory (perfectSupported (j ⁻¹ᵁ T).ι)) :
    ∃ B, objects j T (A ⨿ B) := by
  obtain ⟨R, C, hR, hC, he⟩ := hc A.obj A.property
  exact coprod_complement_of_complex_complement j T A C hC ⟨R, hR, he⟩

end AlgebraicGeometry.Scheme.Modules.SupportedOpenDerivedImage

attribute [colib_tag "COL-0334",
  colib_ref "quillen"
    "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/SupportedOpenDerivedImage/\
    Complements.lean:44-76"
    "adaptation"
    "Actual native complex complements give chosen coproduct membership \
    by a genuine colimit comparison"]
  AlgebraicGeometry.Scheme.Modules.SupportedOpenDerivedImage.coprod_complement_of_complex_complement
  AlgebraicGeometry.Scheme.Modules.SupportedOpenDerivedImage.coprod_complement
