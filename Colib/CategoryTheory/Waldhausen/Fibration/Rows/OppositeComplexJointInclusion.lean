/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.OppositeComplexJoint
public import Colib.CategoryTheory.Waldhausen.SubcategoryInclusion

/-!
# Coherence of the common opposite-complex cylinder under inclusion

An actual inclusion of replete extension-closed complex subcategories preserves
opposite admissible cofibrations and the original weak maps. Both components
use the same ambient cylinder, so the joint-functor comparison has identity
components. The original first endpoint, second endpoint, and projection are
proved compatible in both directions; these equations are additional to the
joint-arrow natural isomorphism.
-/
/-! Implementation provenance:
`Quillen/Waldhausen/Fibration/Rows/OppositeComplexJointInclusion.lean` at
Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The actual complexes, maps and independent universes are retained. -/

@[expose] public section

open CochainComplex


open CategoryTheory.ExactCategory



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
attribute [local instance] Abelian.hasFiniteBiproducts
namespace CategoryTheory.Waldhausen
variable {C : Type u} [Category.{v} C] [Abelian C]
variable (P Q : ObjectProperty (CochainComplex C ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex C ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  [Q.ContainsZero] [Q.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex C ℤ)).IsExtensionClosed Q]
  [Q.IsClosedUnderFiniteProducts] (h : P ≤ Q)

lemma oppositeSubcategoryInclusion_exact :
    IsExact (oppositeComplexSubcategory P).cof (oppositeComplexSubcategory P).weq
      (oppositeComplexSubcategory Q).cof (oppositeComplexSubcategory Q).weq
      (ObjectProperty.ιOfLE h).op where
  zero hZ := (ObjectProperty.ιOfLE h).op.map_isZero hZ
  cofibration f hf := (subcategoryExactInclusion P Q h).map_deflation f.unop hf
  weak _ hf := hf
  pushout hi hs := by
    exact ((subcategoryExactInclusion P Q h).map_isPullback hs.unop hi).op

variable (hP : ∀ K, P K → P (K⟦(-1 : ℤ)⟧))
  (hQ : ∀ K, Q K → Q (K⟦(-1 : ℤ)⟧))

/-- Inclusion uses the same actual opposite-complex cylinder, with unchanged
underlying joint arrow; only the proved object membership is forgotten. -/
def oppositeComplexJointDataInclusionIso :
    (oppositeComplexJointData P hP).joint ⋙
      ExtensionCategory.postcompose (oppositeComplexSubcategory P) (oppositeComplexSubcategory Q)
        (oppositeSubcategoryInclusion_exact P Q h) ≅
    (ObjectProperty.ιOfLE h).op.mapArrow ⋙ (oppositeComplexJointData Q hQ).joint :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro A B f
    change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    simp only [Category.comp_id, Category.id_comp]
    rfl)

/-- The common cylinder comparison retains the original first endpoint. -/
lemma oppositeComplexJointDataInclusionIso_inl (f : Arrow P.FullSubcategoryᵒᵖ) :
    (ObjectProperty.ιOfLE h).op.map ((oppositeComplexJointData P hP).inl.app f) ≫
      ((oppositeComplexJointDataInclusionIso P Q h hP hQ).app f).hom.hom.left =
    (oppositeComplexJointData Q hQ).inl.app ((ObjectProperty.ιOfLE h).op.mapArrow.obj f) := by
  change _ ≫ 𝟙 _ = _
  rw [Category.comp_id]
  rfl

/-- The common cylinder comparison retains the original second endpoint. -/
lemma oppositeComplexJointDataInclusionIso_inr (f : Arrow P.FullSubcategoryᵒᵖ) :
    (ObjectProperty.ιOfLE h).op.map ((oppositeComplexJointData P hP).inr.app f) ≫
      ((oppositeComplexJointDataInclusionIso P Q h hP hQ).app f).hom.hom.left =
    (oppositeComplexJointData Q hQ).inr.app ((ObjectProperty.ιOfLE h).op.mapArrow.obj f) := by
  change _ ≫ 𝟙 _ = _
  rw [Category.comp_id]
  rfl

/-- The common cylinder comparison retains the original weak projection. -/
lemma oppositeComplexJointDataInclusionIso_projection (f : Arrow P.FullSubcategoryᵒᵖ) :
    ((oppositeComplexJointDataInclusionIso P Q h hP hQ).app f).hom.hom.right ≫
      (oppositeComplexJointData Q hQ).projection.app ((ObjectProperty.ιOfLE h).op.mapArrow.obj f) =
    (ObjectProperty.ιOfLE h).op.map ((oppositeComplexJointData P hP).projection.app f) := by
  change 𝟙 _ ≫ _ = _
  rw [Category.id_comp]
  rfl

/-- Inverse orientation for the actual weak-arrow endpoint construction. -/
lemma oppositeComplexJointDataInclusionIso_inv_inl (f : Arrow P.FullSubcategoryᵒᵖ) :
    (oppositeComplexJointData Q hQ).inl.app ((ObjectProperty.ιOfLE h).op.mapArrow.obj f) ≫
      ((oppositeComplexJointDataInclusionIso P Q h hP hQ).inv.app f).hom.left =
    (ObjectProperty.ιOfLE h).op.map ((oppositeComplexJointData P hP).inl.app f) := by
  change _ ≫ 𝟙 _ = _
  rw [Category.comp_id]
  rfl

lemma oppositeComplexJointDataInclusionIso_inv_inr (f : Arrow P.FullSubcategoryᵒᵖ) :
    (oppositeComplexJointData Q hQ).inr.app ((ObjectProperty.ιOfLE h).op.mapArrow.obj f) ≫
      ((oppositeComplexJointDataInclusionIso P Q h hP hQ).inv.app f).hom.left =
    (ObjectProperty.ιOfLE h).op.map ((oppositeComplexJointData P hP).inr.app f) := by
  change _ ≫ 𝟙 _ = _
  rw [Category.comp_id]
  rfl

lemma oppositeComplexJointDataInclusionIso_inv_projection (f : Arrow P.FullSubcategoryᵒᵖ) :
    ((oppositeComplexJointDataInclusionIso P Q h hP hQ).inv.app f).hom.right ≫
      (ObjectProperty.ιOfLE h).op.map ((oppositeComplexJointData P hP).projection.app f) =
    (oppositeComplexJointData Q hQ).projection.app ((ObjectProperty.ιOfLE h).op.mapArrow.obj f)
      := by
  change 𝟙 _ ≫ _ = _
  rw [Category.id_comp]
  rfl

end CategoryTheory.Waldhausen

attribute [colib_tag "COL-0311",
  colib_ref "quillen" "Quillen/Waldhausen/Fibration/Rows/OppositeComplexJointInclusion.lean:48-124"
    "adaptation" "Literal inclusion and all original forward and inverse endpoint equations"]
  CategoryTheory.Waldhausen.oppositeSubcategoryInclusion_exact
  CategoryTheory.Waldhausen.oppositeComplexJointDataInclusionIso
  CategoryTheory.Waldhausen.oppositeComplexJointDataInclusionIso_inv_inl
  CategoryTheory.Waldhausen.oppositeComplexJointDataInclusionIso_inv_inr
  CategoryTheory.Waldhausen.oppositeComplexJointDataInclusionIso_inv_projection
