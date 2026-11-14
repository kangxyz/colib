/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusSectionProduct

/-!
# Descent of the second section factor to the actual reduced weight-one torus

Use the existing actual quotient isomorphism, not a new
replacement quotient or an arbitrary splitting of the original epimorphism.
The parameter unit-axis theorem supplies the whole kernel relation.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Opposite AlgebraicGeometry.Scheme
universe u
namespace AlgebraicGeometry.PresheafWithTransfers
variable (k : Type u) [Field k]
variable (U : SmoothSite (Spec (CommRingCat.of k))) (q : ℕ)
variable (s : sections (reducedTorus k q) (Cor.mk U))

/-- The original product after the canonical one-torus representable isomorphism. -/
def sectionProductRawSecond : sections (torusRepresentable k 1) (Cor.mk U) →+
    sections (reducedTorus k (q + 1)) (Cor.mk U) where
  toFun t := reducedTorusSectionProduct k U q s
    (((torusRepresentableOneIso k).hom.hom.app (op (Cor.mk U)) t).down)
  map_zero' := by
    simp only [map_zero]
    change reducedTorusSectionProduct k U q s 0 = 0
    simp [reducedTorusSectionProduct]
  map_add' t u := by
    simp only [map_add]
    exact reducedTorusSectionProduct_add_right k U q s _ _

/-- Every original weight-one axis relation is killed, not just the base-point graph. -/
theorem sectionProductRawSecond_kills_relations :
    torusIdentityRelations k 1 (Cor.mk U) ≤ (sectionProductRawSecond k U q s).ker := by
  unfold torusIdentityRelations
  apply iSup_le
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rintro t ⟨r, rfl⟩
  change reducedTorusSectionProduct k U q s
    (((torusRepresentableOneIso k).hom.hom.app (op (Cor.mk U))
      ((torusIdentityAxis k 1 0).hom.app (op (Cor.mk U)) r)).down) = 0
  have he := congrArg (fun a => a.hom.app (op (Cor.mk U)) r) (torusIdentityAxis_one k)
  change (torusRepresentableOneIso k).hom.hom.app (op (Cor.mk U))
      ((torusIdentityAxis k 1 0).hom.app (op (Cor.mk U)) r) =
    (torusOneRepresentable k).hom.app (op (Cor.mk U)) r at he
  rw [he]
  exact reducedTorusSectionProduct_unit_axis k U q s r.down

/-- The second argument descends to the actual reducedTorus(1) sections. -/
def reducedTorusBinarySectionProduct :
    sections (reducedTorus k 1) (Cor.mk U) →+
      sections (reducedTorus k (q + 1)) (Cor.mk U) :=
  (QuotientAddGroup.lift (torusIdentityRelations k 1 (Cor.mk U))
    (sectionProductRawSecond k U q s) (sectionProductRawSecond_kills_relations k U q s)).comp
    (reducedTorusSectionsIsoQuotient k 1 (Cor.mk U)).hom.hom

end AlgebraicGeometry.PresheafWithTransfers
