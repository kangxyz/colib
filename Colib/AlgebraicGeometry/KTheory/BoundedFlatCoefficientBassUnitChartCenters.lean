/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassUnitChartIdentity
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH1ProductRowCenter
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH1ProductColumnCenter

/-! The original first and middle normalized centers of both raw Bass identity charts.
Adapted from `CoefficientBassUnitHZeroNodes.lean` at Quillen
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. No top/bottom collisions are asserted. -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Opposite CategoryTheory.Waldhausen.IteratedS
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassUnitHZeroNodes

open BoundedFlatCoefficientBassH1Join

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn
local notation "binaryModelSourceMap" => BoundedFlatPerfectBinarySimplex.sourceMap
local notation "binaryModelTargetMap" => BoundedFlatPerfectBinarySimplex.targetMap
local notation "binaryModelTotal" => BoundedFlatPerfectBinarySimplex.total

private theorem binary_target_transport {A B C : Scheme.{u}}
    (p p' : B ⟶ A) (q q' : C ⟶ B) (hp : p = p') (hq : q = q')
    (F : asSmallCategory (W A) ⟶ asSmallCategory (W C))
    (δ : F.hom.toFunctor ≅ (binaryModelSourceMap q p).hom.toFunctor) :
    ModelSimplex.reanchorNode (δ ≪≫ eqToIso (by subst p'; subst q'; rfl))
        (⟨binaryModelTargetMap q' p', binaryModelTotal q' p'⟩ :
          Σ G : asSmallCategory (W A) ⟶
            asSmallCategory (W C),
            (binaryModelSourceMap q' p').hom.toFunctor ≅ G.hom.toFunctor) =
      ⟨binaryModelTargetMap q p, δ ≪≫ binaryModelTotal q p⟩ := by
  subst p'
  subst q'
  simp only [eqToIso_refl, Iso.trans_refl, ModelSimplex.reanchorNode]

section Rectangle
variable {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B)
  (F : asSmallCategory (W A) ⟶ asSmallCategory (W C))
  (δ : F.hom.toFunctor ≅ (binaryModelSourceMap q p).hom.toFunctor)

/-- Its first normalized chart source retains the true binary total reference. -/
theorem rectangle_first_source : rectangleNodes p q F δ 9 =
    ⟨binaryModelTargetMap q p, δ ≪≫ binaryModelTotal q p⟩ := by
  unfold rectangleNodes
  rw [projection_first_normal]
  change ModelSimplex.reanchorNode (δ ≪≫ eqToIso (rectangleSourceEq p q))
    (ModelSimplex.reanchorNode (eqToIso (projection_first_source_eq p q (𝟙 C) (q ≫ p) rfl))
      ⟨binaryModelTargetMap (𝟙 C ≫ q) p,
        binaryModelTotal (𝟙 C ≫ q) p⟩) = _
  rw [ModelSimplex.reanchorNode_assoc, Iso.trans_assoc, eqToIso_trans]
  exact binary_target_transport p p q (𝟙 C ≫ q) rfl (Category.id_comp q).symm F δ

/-- The middle normalized chart source has exactly that same original binary total reference. -/
theorem rectangle_middle_source : rectangleNodes p q F δ 5 =
    ⟨binaryModelTargetMap q p, δ ≪≫ binaryModelTotal q p⟩ := by
  unfold rectangleNodes
  rw [projection_middle_normal]
  change ModelSimplex.reanchorNode (δ ≪≫ eqToIso (rectangleSourceEq p q))
    (ModelSimplex.reanchorNode (eqToIso (projection_middle_source_eq p q q (𝟙 B) (𝟙 C)
      (by simp) (q ≫ p) rfl))
      ⟨binaryModelTargetMap q (𝟙 B ≫ p),
        binaryModelTotal q (𝟙 B ≫ p)⟩) = _
  rw [ModelSimplex.reanchorNode_assoc, Iso.trans_assoc, eqToIso_trans]
  exact binary_target_transport p (𝟙 B ≫ p) q q (Category.id_comp p).symm rfl F δ

end Rectangle

variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)
  (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)

/-- The first native chart source is its original normalized total, with full transport. -/
theorem chart_first_source : chartNodes P a α ha 9 =
    ⟨binaryModelTargetMap (coefficientMap P (α.app a))
      (polynomialProjection P a), chartProjectionIso P a α ha ≪≫
        binaryModelTotal (coefficientMap P (α.app a))
          (polynomialProjection P a)⟩ :=
  (chart_identity P a α ha 9).trans (rectangle_first_source _ _ _ _)

/-- The two native rectangle rows retain the same normalized source and original reference. -/
theorem chart_middle_source : chartNodes P a α ha 5 =
    ⟨binaryModelTargetMap (coefficientMap P (α.app a))
      (polynomialProjection P a), chartProjectionIso P a α ha ≪≫
        binaryModelTotal (coefficientMap P (α.app a))
          (polynomialProjection P a)⟩ :=
  (chart_identity P a α ha 5).trans (rectangle_middle_source _ _ _ _)

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassUnitHZeroNodes
