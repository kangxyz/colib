/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusSectionDescent

/-! # Generator formula for the actual descended section product -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme
universe u v
namespace AlgebraicGeometry.PresheafWithTransfers
variable (k : Type u) [Field k]

private theorem quotient_transport_mk {A : Type v} [AddCommGroup A]
    (R S : AddSubgroup A) (h : R = S) (t : A) :
    (eqToIso (congrArg (fun T : AddSubgroup A => AddCommGrpCat.of (A ⧸ T)) h)).hom
      (QuotientAddGroup.mk t) = QuotientAddGroup.mk t := by
  subst S
  rfl

/-- The existing cokernel-quotient comparison sends each actual represented
section to its original quotient class. -/
theorem reducedTorusSectionsIsoQuotient_apply_generator (q : ℕ) (X : Cor k)
    (t : sections (torusRepresentable k q) X) :
    (reducedTorusSectionsIsoQuotient k q X).hom
      ((toReducedTorus k q).hom.app (op X) t) =
      QuotientAddGroup.mk t := by
  change (((toReducedTorus k q).hom.app (op X)) ≫
    (reducedTorusSectionsIsoQuotient k q X).hom) t = _
  simp only [reducedTorusSectionsIsoQuotient, Iso.trans_hom]
  change ((((evaluation (Cor k)ᵒᵖ AddCommGrpCat).obj (op X)).map
    (cokernel.π (torusRelation k q))) ≫ _) t = _
  rw [PreservesCokernel.π_iso_hom_assoc]
  simp only [AddCommGrpCat.cokernelIsoQuotient]
  change ((cokernel.π ((torusRelation k q).app (op X))) ≫ _) t = _
  rw [cokernel.π_desc_assoc]
  exact quotient_transport_mk _ _ (range_torusRelation k q X) t

/-- On the original quotient generators the descended product is the original
section product, with the canonical one-torus representable identification. -/
theorem reducedTorusBinarySectionProduct_generator
    (U : SmoothSite (Spec (CommRingCat.of k))) (q : ℕ)
    (s : sections (reducedTorus k q) (Cor.mk U))
    (t : sections (torusRepresentable k 1) (Cor.mk U)) :
    reducedTorusBinarySectionProduct k U q s
      ((toReducedTorus k 1).hom.app (op (Cor.mk U)) t) =
      sectionProductRawSecond k U q s t := by
  change (QuotientAddGroup.lift _ (sectionProductRawSecond k U q s)
    (sectionProductRawSecond_kills_relations k U q s))
    ((reducedTorusSectionsIsoQuotient k 1 (Cor.mk U)).hom
      ((toReducedTorus k 1).hom.app (op (Cor.mk U)) t)) = _
  rw [reducedTorusSectionsIsoQuotient_apply_generator]
  rfl

end AlgebraicGeometry.PresheafWithTransfers
