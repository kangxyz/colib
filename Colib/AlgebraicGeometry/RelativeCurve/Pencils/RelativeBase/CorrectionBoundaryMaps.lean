/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.ProductBoundary
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.MarkedCoordinate

/-!
# Boundary maps for the correction parameter

The original puncture restricts the first parameter. The entire marked
fiber has the source and target maps induced by that restriction.

Adapted from `Motivic/Aglib/AlgebraicGeometry/RelativeCurve/Pencils/Correction/NormalizedUnit.lean`
at a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Ample Stacks.Divisors
open Stacks.Morphisms

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

section BoundaryMap

variable {X T B : Scheme.{u}} (F : X ⟶ T) (U : T.Opens)
  (m : B ⟶ T) (l : B ⟶ U.toScheme) (hl : l ≫ U.ι = m)

/-- Restrict the entire inverse boundary to the same good open. -/
def normQuotientBoundaryMap : pullback F m ⟶ pullback F U.ι :=
  (IsPullback.of_hasPullback F U.ι).lift (pullback.fst F m) (pullback.snd F m ≫ l) (by
    rw [Category.assoc, hl]
    exact pullback.condition)

@[reassoc (attr := simp)]
theorem normQuotientBoundaryMap_fst :
    normQuotientBoundaryMap F U m l hl ≫ pullback.fst F U.ι = pullback.fst F m :=
  (IsPullback.of_hasPullback F U.ι).lift_fst _ _ _

@[reassoc (attr := simp)]
theorem normQuotientBoundaryMap_snd :
    normQuotientBoundaryMap F U m l hl ≫ pullback.snd F U.ι = pullback.snd F m ≫ l :=
  (IsPullback.of_hasPullback F U.ι).lift_snd _ _ _

theorem normQuotientBoundaryMap_isPullback :
    IsPullback (normQuotientBoundaryMap F U m l hl) (pullback.snd F m)
      (pullback.snd F U.ι) l := by
  have H : IsPullback (pullback.fst F m) (pullback.snd F m) F (l ≫ U.ι) :=
    hl.symm ▸ IsPullback.of_hasPullback F m
  exact H.of_right' (IsPullback.of_hasPullback F U.ι)

end BoundaryMap

section Parameter

variable {S X P A Z : Scheme.{u}} (q : X ⟶ S) (π : P ⟶ S) (jA : X ⟶ P)
  (hA : jA ≫ π = q) (a : A ⟶ X)

/-- The literal first-parameter restriction of the original target product. -/
def correctionTargetParameterMap : pullback (a ≫ q) π ⟶ pullback (jA ≫ π) π :=
  pullback.map (a ≫ q) π (jA ≫ π) π a (𝟙 P) (𝟙 S)
    ((Category.comp_id _).trans (congrArg (a ≫ ·) hA.symm)) (by simp)

@[reassoc (attr := simp)]
theorem correctionTargetParameterMap_fst :
    correctionTargetParameterMap q π jA hA a ≫ pullback.fst (jA ≫ π) π =
      pullback.fst (a ≫ q) π ≫ a := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem correctionTargetParameterMap_snd :
    correctionTargetParameterMap q π jA hA a ≫ pullback.snd (jA ≫ π) π =
      pullback.snd (a ≫ q) π := (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The same whole marked boundary with its original structure morphism to the base. -/
def correctionMarkBaseIso (z : Z ⟶ X) :
    pullback (a ≫ q) ((z ≫ jA) ≫ π) ≅ pullback (a ≫ q) (z ≫ q) :=
  pullback.congrHom rfl ((Category.assoc z jA π).trans (congrArg (z ≫ ·) hA))

/-- The whole marked boundary changes only its first factor. -/
def correctionMarkToTargetProduct (z : Z ⟶ X) :
    pullback (a ≫ q) ((z ≫ jA) ≫ π) ⟶ pullback (jA ≫ π) (z ≫ jA ≫ π) :=
  pullback.map (a ≫ q) ((z ≫ jA) ≫ π) (jA ≫ π) (z ≫ jA ≫ π) a (𝟙 Z) (𝟙 S)
    ((Category.comp_id _).trans (congrArg (a ≫ ·) hA.symm))
    (by simp only [Category.comp_id, Category.id_comp, Category.assoc])

theorem correctionMarkToTargetProduct_map (z : Z ⟶ X) :
    correctionMarkToTargetProduct q π jA hA a z ≫ markedProductMap π jA z =
      retainedProductInclusion (a ≫ q) π (z ≫ jA) ≫ correctionTargetParameterMap q π jA hA a := by
  apply pullback.hom_ext
  · simp [correctionMarkToTargetProduct, markedProductMap, pullback.map, Category.assoc]
  · simp [correctionMarkToTargetProduct, markedProductMap, pullback.map, Category.assoc]

theorem correctionMarkToTargetProduct_coordinate (z : Z ⟶ X) :
    correctionMarkToTargetProduct q π jA hA a z ≫
        markedProductToTarget q π jA (𝟙 X) (hA.trans (Category.id_comp q).symm)
          z z (Category.comp_id z) =
      (correctionMarkBaseIso q π jA hA a z).hom ≫ correctionProductToTarget q z a := by
  apply pullback.hom_ext
  · simp [correctionMarkToTargetProduct, correctionMarkBaseIso, pullback.congrHom_hom,
      pullback.map, correctionProductToTarget, retainedSourceChange_fst, Category.assoc]
  · simp [correctionMarkToTargetProduct, correctionMarkBaseIso, pullback.congrHom_hom,
      pullback.map, correctionProductToTarget, retainedSourceChange_snd, Category.assoc]

/-- The actual product marked section agrees with the correction's full marked leg. -/
theorem correctionMarkToSourceProduct_map {C Y : Scheme.{u}}
    (f : C ⟶ P) (j : Y ⟶ C) (p : Y ⟶ X) (hB : j ≫ (f ≫ π) = p ≫ q)
    (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z)
    (H : IsPullback s (𝟙 Z) (j ≫ f) (z ≫ jA)) :
    (correctionMarkBaseIso q π jA hA a z).hom ≫
        psiZeroInclusion q (f ≫ π) j p hB a z s hs =
      productMarkedSection (a ≫ q) π f (z ≫ jA) j s H ≫
        retainedProductInclusion (a ≫ q) (f ≫ π) j := by
  apply pullback.hom_ext
  · simp [correctionMarkBaseIso, psiZeroInclusion, pullback.congrHom_hom, pullback.map,
      productMarkedSection, productSecondMap_fst, Category.assoc]
  · simp [correctionMarkBaseIso, psiZeroInclusion, pullback.congrHom_hom, pullback.map,
      productMarkedSection, Category.assoc]

end Parameter

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

end
