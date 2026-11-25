/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassUnitChartCenters
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumSplitUnitRows
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectProjectionRightRows

/-! The two original split-unit right-column forms and their full chart-to-side identifications.
Adapted from `ProjectionChartRows.lean` and `CoefficientBassUnitHZeroNodes.lean` at Quillen
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS SmallWaldhausenCategory
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Simplicial

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassUnitHZeroNodes

open ModelSimplex BoundedFlatPerfectProjectionBinaryRows BoundedFlatPerfectOriginalUnitSquareSimplex
open BoundedFlatCoefficientBassH1Join (nativeMiddleReference)

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn
local notation "binaryModelSourceMap" => BoundedFlatPerfectBinarySimplex.sourceMap
local notation "binaryModelTotal" => BoundedFlatPerfectBinarySimplex.total
local notation "projectionRefAnchor" => BoundedFlatPerfectProjectionReference.anchor
local notation "projectionRefNodes" => BoundedFlatPerfectProjectionReference.nodes
local notation "projectionRefReference" => BoundedFlatPerfectProjectionReference.reference
local notation "bottomSrc" => BoundedFlatCoefficientBassUnitBottom.source

/-- An identity at the reference node is unchanged under fixed precomposition. -/
theorem pre_reference_source {V M T : WideSubcategory preservesZero.{u}} (F : V ⟶ T)
    (J : V ⟶ M) {H : M ⟶ T} (ρ : F.hom.toFunctor ≅ (J ≫ H).hom.toFunctor) :
    preReferenceNode F J ρ ⟨H, Iso.refl _⟩ = ⟨J ≫ H, ρ⟩ := by
  have h : isoWhiskerLeft J.hom.toFunctor (Iso.refl H.hom.toFunctor) =
      Iso.refl (J.hom.toFunctor ⋙ H.hom.toFunctor) := by
    rw [isoWhiskerLeft_refl]
  exact congrArg (fun ν : F.hom.toFunctor ≅ (J ≫ H).hom.toFunctor ↦
    (⟨J ≫ H, ν⟩ : CommonReferenceNerve.Node F))
    ((congrArg (fun τ ↦ ρ ≪≫ τ) h).trans (Iso.trans_refl ρ))

theorem pre_anchor_node {V M T : WideSubcategory preservesZero.{u}}
    (F : V ⟶ T) (P : V ⟶ M) {H L : M ⟶ T}
    (ρ : F.hom.toFunctor ≅ (P ≫ H).hom.toFunctor)
    (η : H.hom.toFunctor ≅ L.hom.toFunctor)
    (N : Σ G : M ⟶ T, L.hom.toFunctor ≅ G.hom.toFunctor) :
    preReferenceNode F P ρ (reanchorNode η N) =
      preReferenceNode F P (ρ ≪≫ isoWhiskerLeft P.hom.toFunctor η) N := by
  rcases N with ⟨G, σ⟩
  apply congrArg (fun ν : F.hom.toFunctor ≅ (P ≫ G).hom.toFunctor ↦
    (⟨P ≫ G, ν⟩ : Σ G : V ⟶ T, F.hom.toFunctor ≅ G.hom.toFunctor))
  change ρ ≪≫ isoWhiskerLeft P.hom.toFunctor (η ≪≫ σ) = _
  rw [isoWhiskerLeft_trans, Iso.trans_assoc]

private theorem anchor_pre_node {V M T : WideSubcategory preservesZero.{u}}
    {F K : V ⟶ T} (J : V ⟶ M) {H : M ⟶ T}
    (η : F.hom.toFunctor ≅ K.hom.toFunctor)
    (ρ : K.hom.toFunctor ≅ (J ≫ H).hom.toFunctor)
    (N : Σ G : M ⟶ T, H.hom.toFunctor ≅ G.hom.toFunctor) :
    reanchorNode η (preReferenceNode K J ρ N) =
      preReferenceNode F J (η ≪≫ ρ) N := by
  rcases N with ⟨G, σ⟩
  apply congrArg (fun ν : F.hom.toFunctor ≅ (J ≫ G).hom.toFunctor ↦
    (⟨J ≫ G, ν⟩ : Σ G : V ⟶ T, F.hom.toFunctor ≅ G.hom.toFunctor))
  exact (Iso.trans_assoc _ _ _).symm

section Rectangle

variable {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B)

private abbrev identityProjection := projectionRefReference (𝟙 C) (q ≫ p)

private def nativeFirstReference : (identityProjection p q).hom.toFunctor ≅
    (BoundedFlatPerfectTripleSimplex.source (𝟙 C) q p).hom.toFunctor :=
  eqToIso (projectionRefAnchor p q (𝟙 C) (q ≫ p) rfl)

private theorem native_first_right_row (i : Fin 3) :
    projectionRefNodes p q p q (𝟙 A) (𝟙 B) (𝟙 C) (by simp) (by simp) (q ≫ p) rfl
      (BoundedFlatPerfectDoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i)) =
      preReferenceNode (identityProjection p q) (normalizedMap p)
        (rightRowReference (identityProjection p q) (𝟙 C) q p (nativeFirstReference p q))
        (binaryNodes (𝟙 C) q i) := by
  simpa only [projectionNativeNode, reanchorNodes, reanchorNode, eqToIso_refl, Iso.refl_trans,
    projectionFirstReference, nativeFirstReference, preBinaryNodes, preReferenceNode] using
    (projection_first_right_row p q p q (𝟙 A) (𝟙 B) (𝟙 C) (by simp) (by simp)
      (q ≫ p) rfl (identityProjection p q) rfl i)

private theorem native_middle_right_row (i : Fin 3) :
    projectionRefNodes p q p q (𝟙 A) (𝟙 B) (𝟙 C) (by simp) (by simp) (q ≫ p) rfl
      (BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i)) =
      preReferenceNode (identityProjection p q) (normalizedMap p)
        (rightRowReference (identityProjection p q) q (𝟙 B) p
          (nativeMiddleReference p q q (𝟙 B) (𝟙 C) (by simp) (q ≫ p) rfl))
        (binaryNodes q (𝟙 B) i) := by
  simpa only [projectionNativeNode, reanchorNodes, reanchorNode, eqToIso_refl, Iso.refl_trans,
    projectionMiddleReference, projectionFirstReference, nativeMiddleReference,
    preBinaryNodes, preReferenceNode] using
    (projection_middle_right_row p q p q (𝟙 A) (𝟙 B) (𝟙 C) (by simp) (by simp)
      (q ≫ p) rfl (identityProjection p q) rfl i)

variable (F : asSmallCategory (W A) ⟶ asSmallCategory (W C))
  (δ : F.hom.toFunctor ≅ (binaryModelSourceMap q p).hom.toFunctor)

/-- The original chart unit vertices with the unchanged polynomial precomposition. -/
def rectangleSideNodes (i : Fin 8) :
    Σ G : asSmallCategory (W A) ⟶
      asSmallCategory (W C), F.hom.toFunctor ≅ G.hom.toFunctor :=
  preReferenceNode F (sourceMap p) (δ ≪≫ binaryModelTotal q p)
    ⟨vertices q i, references q i⟩

/-- The reference isomorphism to the precomposed first binary row. -/
def firstRowAnchor : F.hom.toFunctor ≅
    (sourceMap p ≫ binaryModelSourceMap (𝟙 C) q).hom.toFunctor :=
  (δ ≪≫ eqToIso (rectangleSourceEq p q)) ≪≫
    rightRowReference (projectionRefReference (𝟙 C) (q ≫ p)) (𝟙 C) q p
      (eqToIso (projectionRefAnchor p q (𝟙 C) (q ≫ p) rfl))

/-- The reference isomorphism to the precomposed middle binary row. -/
def middleRowAnchor : F.hom.toFunctor ≅
    (sourceMap p ≫ binaryModelSourceMap q (𝟙 B)).hom.toFunctor :=
  (δ ≪≫ eqToIso (rectangleSourceEq p q)) ≪≫
    rightRowReference (projectionRefReference (𝟙 C) (q ≫ p)) q (𝟙 B) p
      (nativeMiddleReference p q q (𝟙 B) (𝟙 C) (by simp) (q ≫ p) rfl)

/-- The original first H0 row remains its genuine precomposed binary row. -/
theorem rectangle_first_row_form (i : Fin 3) :
    rectangleNodes p q F δ
      (BoundedFlatPerfectDoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i)) =
      preReferenceNode F (sourceMap p) (firstRowAnchor p q F δ)
        (binaryNodes (𝟙 C) q i) := by
  unfold rectangleNodes
  rw [native_first_right_row]
  unfold firstRowAnchor
  exact anchor_pre_node (F := F) (K := identityProjection p q)
    (H := binaryModelSourceMap (𝟙 C) q) (sourceMap p)
    (δ ≪≫ eqToIso (rectangleSourceEq p q))
    (rightRowReference (identityProjection p q) (𝟙 C) q p (nativeFirstReference p q))
    (binaryNodes (𝟙 C) q i)

/-- The other H0 chart row retains the actual middle-square reference transport. -/
theorem rectangle_middle_row_form (i : Fin 3) :
    rectangleNodes p q F δ
      (BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i)) =
      preReferenceNode F (sourceMap p) (middleRowAnchor p q F δ)
        (binaryNodes q (𝟙 B) i) := by
  unfold rectangleNodes
  rw [native_middle_right_row]
  exact anchor_pre_node _ _ _ _

/-- The side's first unit row uses the same old binary normalization with source transport. -/
theorem rectangle_side_right_form (i : Fin 3) :
    rectangleSideNodes p q F δ (![0, 1, 2] i) =
      preReferenceNode F (sourceMap p)
        ((δ ≪≫ binaryModelTotal q p) ≪≫
          isoWhiskerLeft (sourceMap p).hom.toFunctor (eqToIso (rightBinarySourceEq q)))
        (binaryNodes (𝟙 C) q i) := by
  unfold rectangleSideNodes
  rw [unit_right_row]
  exact pre_anchor_node _ _ _ _ _

/-- The other side row retains its separate original unit transport. -/
theorem rectangle_side_left_form (i : Fin 3) :
    rectangleSideNodes p q F δ (![0, 4, 5] i) =
      preReferenceNode F (sourceMap p)
        ((δ ≪≫ binaryModelTotal q p) ≪≫
          isoWhiskerLeft (sourceMap p).hom.toFunctor (eqToIso (leftBinarySourceEq q)))
        (binaryNodes q (𝟙 B) i) := by
  unfold rectangleSideNodes
  rw [unit_left_row]
  exact pre_anchor_node _ _ _ _ _

/-- Equality of the complete source node identifies all three actual first-row nodes. -/
theorem rectangle_side_right (i : Fin 3) :
    rectangleNodes p q F δ
      (BoundedFlatPerfectDoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i)) =
      rectangleSideNodes p q F δ (![0, 1, 2] i) := by
  apply pre_families_match F (sourceMap p) (binaryModelSourceMap (𝟙 C) q)
    (binaryNodes (𝟙 C) q) (rectangle_first_row_form p q F δ)
      (rectangle_side_right_form p q F δ) 0 ?_ i
  change rectangleNodes p q F δ 9 =
    preReferenceNode F (sourceMap p) (δ ≪≫ binaryModelTotal q p)
      ⟨sourceMap q, Iso.refl _⟩
  exact (rectangle_first_source p q F δ).trans
    (pre_reference_source F (sourceMap p) (H := sourceMap q)
      (δ ≪≫ binaryModelTotal q p)).symm

/-- The complete middle row follows from the same actual source and its native binary data. -/
theorem rectangle_side_left (i : Fin 3) :
    rectangleNodes p q F δ
      (BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i)) =
      rectangleSideNodes p q F δ (![0, 4, 5] i) := by
  apply pre_families_match F (sourceMap p) (binaryModelSourceMap q (𝟙 B))
    (binaryNodes q (𝟙 B)) (rectangle_middle_row_form p q F δ)
      (rectangle_side_left_form p q F δ) 0 ?_ i
  change rectangleNodes p q F δ 9 =
    preReferenceNode F (sourceMap p) (δ ≪≫ binaryModelTotal q p)
      ⟨sourceMap q, Iso.refl _⟩
  exact (rectangle_first_source p q F δ).trans
    (pre_reference_source F (sourceMap p) (H := sourceMap q)
      (δ ≪≫ binaryModelTotal q p)).symm

end Rectangle


variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- The plus chart's original right binary row keeps all three dependent references. -/
theorem plus_chart_side_right (i : Fin 3) :
    chartNodes P a (underToLaurent R) (laurentPlus_projection P a)
        (BoundedFlatPerfectDoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i)) =
      rectangleSideNodes (polynomialProjection P a) (coefficientMap P ((underToLaurent R).app a))
        (bottomSrc P a) (chartProjectionIso P a (underToLaurent R) (laurentPlus_projection P a))
        (![0, 1, 2] i) :=
  (chart_identity P a (underToLaurent R) (laurentPlus_projection P a) _).trans
    (rectangle_side_right _ _ _ _ i)

/-- The plus chart's original left binary row keeps all three dependent references. -/
theorem plus_chart_side_left (i : Fin 3) :
    chartNodes P a (underToLaurent R) (laurentPlus_projection P a)
        (BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i)) =
      rectangleSideNodes (polynomialProjection P a) (coefficientMap P ((underToLaurent R).app a))
        (bottomSrc P a) (chartProjectionIso P a (underToLaurent R) (laurentPlus_projection P a))
        (![0, 4, 5] i) :=
  (chart_identity P a (underToLaurent R) (laurentPlus_projection P a) _).trans
    (rectangle_side_left _ _ _ _ i)

/-- The minus chart's original right binary row keeps all three dependent references. -/
theorem minus_chart_side_right (i : Fin 3) :
    chartNodes P a (underToLaurentInvert R) (laurentMinus_projection P a)
        (BoundedFlatPerfectDoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i)) =
      rectangleSideNodes (polynomialProjection P a)
        (coefficientMap P ((underToLaurentInvert R).app a))
        (bottomSrc P a)
        (chartProjectionIso P a (underToLaurentInvert R) (laurentMinus_projection P a))
        (![0, 1, 2] i) :=
  (chart_identity P a (underToLaurentInvert R) (laurentMinus_projection P a) _).trans
    (rectangle_side_right _ _ _ _ i)

/-- The minus chart's original left binary row keeps all three dependent references. -/
theorem minus_chart_side_left (i : Fin 3) :
    chartNodes P a (underToLaurentInvert R) (laurentMinus_projection P a)
        (BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i)) =
      rectangleSideNodes (polynomialProjection P a)
        (coefficientMap P ((underToLaurentInvert R).app a))
        (bottomSrc P a)
        (chartProjectionIso P a (underToLaurentInvert R) (laurentMinus_projection P a))
        (![0, 4, 5] i) :=
  (chart_identity P a (underToLaurentInvert R) (laurentMinus_projection P a) _).trans
    (rectangle_side_left _ _ _ _ i)

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassUnitHZeroNodes
