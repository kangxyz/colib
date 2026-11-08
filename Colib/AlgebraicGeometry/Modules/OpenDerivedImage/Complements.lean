/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.OpenDerivedImage.Exact
public import Colib.AlgebraicGeometry.Modules.PerfectJoint

/-!
# Actual native perfect complements and the honest restriction image

The geometric input states exactly that an actual native perfect complex on the open has
an actual native perfect complement whose sum is derived-isomorphic to a global restriction.
It does not assume density, a K-equivalence or a cylinder. The coproduct comparison below
constructs density on the unchanged native perfect category from this precise input.
The geometric qcqs existence theorem is separate and is not asserted here.

Adapted from Quillen's `OpenDerivedImage/Complements.lean` and `GlobalComplements.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory

attribute [local instance] Abelian.hasFiniteBiproducts hasBinaryBiproducts_of_finite_biproducts

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme.Modules.OpenDerivedImage

universe u d

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  [HasDerivedCategory.{d} U.Modules]

/-- The exact outstanding geometric complement statement, in the chosen derived model. -/
def HasPerfectComplements : Prop :=
  ∀ (P : CochainComplex U.Modules ℤ),
    RingedSpace.IsPerfectComplex (X := U.toRingedSpace) P →
    ∃ (R : CochainComplex X.Modules ℤ) (C : CochainComplex U.Modules ℤ),
      RingedSpace.IsPerfectComplex (X := X.toRingedSpace) R ∧
      RingedSpace.IsPerfectComplex (X := U.toRingedSpace) C ∧
      Nonempty (DerivedCategory.Q.obj
          (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj R) ≅
        DerivedCategory.Q.obj (P ⊞ C))

/-- The honest image predicate on the original native perfect category. -/
def objects : ObjectProperty
    (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := U.toRingedSpace))) :=
  fun A => complexObjects j A.obj

local instance (U : Scheme.{u}) : HasFiniteBiproducts
    (CochainComplex (StrictlyPerfect.OXMod.{u, u, u} U.toRingedSpace) ℤ) :=
  Abelian.hasFiniteBiproducts
    (C := CochainComplex (StrictlyPerfect.OXMod.{u, u, u} U.toRingedSpace) ℤ)

local instance (U : Scheme.{u}) : ObjectProperty.IsClosedUnderFiniteProducts
    (RingedSpace.IsPerfectComplex (X := U.toRingedSpace)) :=
  RingedSpace.isPerfectComplex_closedUnderFiniteProducts U.toRingedSpace

local instance (U : Scheme.{u}) : (abelianExactStructure
    (CochainComplex (StrictlyPerfect.OXMod.{u, u, u} U.toRingedSpace) ℤ)).IsExtensionClosed
      (RingedSpace.IsPerfectComplex (X := U.toRingedSpace)) :=
  RingedSpace.isPerfectComplex_extensionClosed U.toRingedSpace

/-- Native finite-product closure gives actual binary biproducts, hence coproducts. -/
instance perfectComplexes_hasBinaryCoproducts (U : Scheme.{u}) :
    HasBinaryCoproducts
      (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := U.toRingedSpace))) := by
  let : HasFiniteBiproducts
      (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := U.toRingedSpace))) :=
    ExactSubcategory.subcategoryHasFiniteBiproducts
      (RingedSpace.IsPerfectComplex (X := U.toRingedSpace))
  exact hasBinaryCoproducts_of_hasBinaryBiproducts

/-- An actual complex complement gives membership of the chosen categorical coproduct
through its genuine universal-property comparison, rather than definitional equality. -/
theorem coprod_complement_of_complex_complement
    (A : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := U.toRingedSpace)))
    (C : CochainComplex U.Modules ℤ)
    (hC : RingedSpace.IsPerfectComplex (X := U.toRingedSpace) C)
    (hAC : complexObjects j (A.obj ⊞ C)) :
    ∃ B, objects j (A ⨿ B) := by
  let B : ObjectProperty.FullSubcategory
      (RingedSpace.IsPerfectComplex (X := U.toRingedSpace)) := ⟨C, hC⟩
  let T : ObjectProperty.FullSubcategory
      (RingedSpace.IsPerfectComplex (X := U.toRingedSpace)) :=
    ⟨A.obj ⊞ B.obj, RingedSpace.isPerfectComplex_X₂_of_shortExact U.toRingedSpace
      (ShortComplex.Splitting.ofHasBinaryBiproduct A.obj B.obj).shortExact
      A.property B.property⟩
  let il : A ⟶ T := ObjectProperty.homMk biprod.inl
  let ir : B ⟶ T := ObjectProperty.homMk biprod.inr
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
  let e : A ⨿ B ≅ T := (coprodIsCoprod A B).coconePointUniqueUpToIso ht
  exact ⟨B, (complexObjects_iff_of_derivedIso j
    (DerivedCategory.Q.mapIso
      ((ObjectProperty.ι (RingedSpace.IsPerfectComplex (X := U.toRingedSpace))).mapIso e))).mpr
        hAC⟩

/-- The displayed geometric input constructs actual coproduct density. -/
theorem coprod_complement (hc : HasPerfectComplements j)
    (A : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := U.toRingedSpace))) :
    ∃ B, objects j (A ⨿ B) := by
  obtain ⟨R, C, hR, hC, he⟩ := hc A.obj A.property
  exact coprod_complement_of_complex_complement j A C hC ⟨R, hR, he⟩

end AlgebraicGeometry.Scheme.Modules.OpenDerivedImage

attribute [colib_tag "COL-0315",
  colib_ref "quillen"
    "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/OpenDerivedImage/\
    Complements.lean:54-81"
    "adaptation"
    "Actual native complex complements give chosen coproduct membership \
    by a genuine colimit comparison"]
  AlgebraicGeometry.Scheme.Modules.OpenDerivedImage.coprod_complement_of_complex_complement
  AlgebraicGeometry.Scheme.Modules.OpenDerivedImage.coprod_complement
