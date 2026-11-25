/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH0BinaryRows
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassMergedBoundarySimplex

/-!
# The actual signed H₀ target nodes in the original Bass 44-simplex

The two comparisons use the actual projection columns and Laurent product
with their original reference transports. Adapted from `BassH0ProjectionColumns.lean`,
`BassBottomPositiveColumn.lean` and `BassBottomNegativeColumn.lean` in Quillen
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Topology
open AlgebraicGeometry.Scheme.BaseChange.Coefficients CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS

universe u v

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH0Merge

open ModelSimplex BoundedFlatPerfectProjectionBinaryRows BoundedFlatPerfectReferenceCoherence
open BoundedFlatCoefficientBassChartBottomReferences CommonReferenceProduct

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn
local notation "N" => boundedAboveFlatPerfectNormalizedPullback
local notation "NC" => boundedAboveFlatPerfectNormalizedPullbackCompIso

section ProjectionColumns

variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)
  (r : C ⟶ A) (hr : q ≫ p = r)
  (F : asSmallCategory (W A) ⟶ asSmallCategory (W C'))
  (e : F.hom.toFunctor = (BoundedFlatPerfectProjectionReference.reference c r).hom.toFunctor)

private theorem projection_left_column (i : Fin 3) :
    projectionNativeNode p q p' q' a b c hp hq r hr F e (rectangleLeftIndex i) =
      binaryColumnNode F c q p
        (e.trans (BoundedFlatPerfectProjectionReference.anchor p q c r hr)) i := by
  change reanchorNode (eqToIso e)
    (BoundedFlatPerfectProjectionReference.nodes p q p' q' a b c hp hq r hr
      (rectangleLeftIndex i)) = _
  rw [native_source_column]
  change (⟨_, eqToIso e ≪≫
    ((eqToIso (BoundedFlatPerfectProjectionReference.anchor p q c r hr) ≪≫ _) ≪≫ _)⟩ :
    Σ G : asSmallCategory (W A) ⟶ asSmallCategory (W C'), F.hom.toFunctor ≅ G.hom.toFunctor) =
    ⟨_, (eqToIso (e.trans (BoundedFlatPerfectProjectionReference.anchor p q c r hr)) ≪≫ _) ≪≫ _⟩
  rw [← Iso.trans_assoc, ← Iso.trans_assoc, eqToIso_trans]; rfl

end ProjectionColumns

private theorem binaryColumnNode_congr {X Y Z T : Scheme.{u}}
    (F : asSmallCategory (W T) ⟶ asSmallCategory (W X))
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    (e : F.hom.toFunctor = (BoundedFlatPerfectTripleSimplex.source f g h).hom.toFunctor)
    {f' : X ⟶ Y} (hf : f = f')
    (e' : F.hom.toFunctor = (BoundedFlatPerfectTripleSimplex.source f' g h).hom.toFunctor)
    (i : Fin 3) :
    binaryColumnNode F f g h e i = binaryColumnNode F f' g h e' i := by
  subst f'
  rfl

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The original bottom total equality at its exact two-factor model functor. -/
theorem bottom_reference_eq
  : (BoundedFlatCoefficientBassOverlap.commonReference P u v).hom.toFunctor =
    (BoundedFlatPerfectBinarySimplex.sourceMap (laurentComposite P u v)
      (laurentPlus P a ≫ polynomialProjection P a)).hom.toFunctor :=
  congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
    (congrArg N (BoundedFlatCoefficientBassBottomCommonFamily.bottom_total P u v).symm)

/-- The original chart projection equation composes with the actual H0 common-reference equality. -/
theorem chart_reference_eq (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a) :
    (BoundedFlatCoefficientBassOverlap.commonReference P u v).hom.toFunctor =
      (BoundedFlatPerfectTripleSimplex.source
        (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v)))
        (coefficientMap P (α.app a)) (polynomialProjection P a)).hom.toFunctor :=
  (reference_eq P u v).trans
    (BoundedFlatPerfectProjectionReference.anchor (polynomialProjection P a)
      (coefficientMap P (α.app a))
      (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v))) (laurentProjection P a) ha)

/-- The complete positive source column uses its original postcomposed binary normalization. -/
theorem plus_source_column (i : Fin 3) :
    nodes P u v (BoundedFlatCoefficientBassH0Diagram.plusFace.toOrderHom (rectangleLeftIndex i)) =
      binaryColumnNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
        (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v)))
        (laurentPlus P a) (polynomialProjection P a)
        (chart_reference_eq P u v (underToLaurent R) (laurentPlus_projection P a)) i := by
  have h := congrArg (fun (node : BoundedFlatCoefficientBassH0Diagram.Node P (u ≫ v)) ↦
      (⟨node.1, eqToIso (reference_eq P u v) ≪≫ node.2⟩ :
        BoundedFlatCoefficientBassOverlap.Node P u v))
    (BoundedFlatCoefficientBassH0Diagram.plus_nodes P (u ≫ v) (rectangleLeftIndex i))
  exact h.trans (projection_left_column
    (polynomialProjection P a) (laurentPlus P a)
    (polynomialProjection P c) (laurentPlus P c)
    (coefficientMap P (u ≫ v)) (coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v)))
    (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v)))
    (polynomialProjection_naturality P (u ≫ v))
    (coefficientMap_naturality_of_natTrans P (underToLaurent R) (u ≫ v))
    (laurentProjection P a) (laurentPlus_projection P a)
    (BoundedFlatCoefficientBassOverlap.commonReference P u v) (reference_eq P u v) i)

/-- The inverse source column retains the separate original inverse-chart binary normalization. -/
theorem minus_source_column (i : Fin 3) :
    nodes P u v (BoundedFlatCoefficientBassH0Diagram.minusFace.toOrderHom (rectangleLeftIndex i)) =
      binaryColumnNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
        (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v)))
        (laurentMinus P a) (polynomialProjection P a)
        (chart_reference_eq P u v (underToLaurentInvert R) (laurentMinus_projection P a)) i := by
  have h := congrArg (fun (node : BoundedFlatCoefficientBassH0Diagram.Node P (u ≫ v)) ↦
      (⟨node.1, eqToIso (reference_eq P u v) ≪≫ node.2⟩ :
        BoundedFlatCoefficientBassOverlap.Node P u v))
    (BoundedFlatCoefficientBassH0Diagram.minus_nodes P (u ≫ v) (rectangleLeftIndex i))
  exact h.trans (projection_left_column
    (polynomialProjection P a) (laurentMinus P a)
    (polynomialProjection P c) (laurentMinus P c)
    (coefficientMap P (u ≫ v)) (coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v)))
    (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v)))
    (polynomialProjection_naturality P (u ≫ v))
    (coefficientMap_naturality_of_natTrans P (underToLaurentInvert R) (u ≫ v))
    (laurentProjection P a) (laurentMinus_projection P a)
    (BoundedFlatCoefficientBassOverlap.commonReference P u v) (reference_eq P u v) i)

section Functors
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
/-- An identity in the second factor leaves the original first-factor whiskering. -/
theorem composition_pair_refl {F₀ F₁ : C ⥤ D} (e : F₀ ≅ F₁) (G : D ⥤ E) :
    (Functor.uncurry.obj (whiskeringLeft C D E)).mapIso (e.prod (Iso.refl G)) =
      isoWhiskerRight e G := by
  rw [composition_pair_iso, isoWhiskerLeft_refl, Iso.trans_refl]
end Functors

/-- The geometric total produces the original positive bottom anchor. -/
theorem bottom_anchor_iso : BoundedFlatCoefficientBassBottomCommonFamily.referenceIso P u v =
    eqToIso (bottom_reference_eq P u v) ≪≫ BoundedFlatPerfectBinarySimplex.total
      (laurentComposite P u v) (laurentPlus P a ≫ polynomialProjection P a) := by
  change smallIso (eqToIso (congrArg N
      (BoundedFlatCoefficientBassBottomCommonFamily.bottom_total P u v).symm) ≪≫
      NC (laurentComposite P u v)
        (laurentPlus P a ≫ polynomialProjection P a)) = _
  rw [smallIso_trans, smallIso_eqToIso]
  rfl

/-- The first three projection-path nodes are the complete original positive binary nodes. -/
theorem projection_plus_nodes (i : Fin 3) :
    BoundedFlatCoefficientBassProjectionPath.nodes P a (Fin.castAdd 2 i) =
      binaryNodes (laurentPlus P a) (polynomialProjection P a) i := by
  fin_cases i <;> rfl

/-- The whole original positive bottom column keeps every actual binary reference isomorphism. -/
theorem bottom_plus_column (i : Fin 3) :
    BoundedFlatCoefficientBassReferenceMerge.nodes P u v
      (BoundedFlatCoefficientBassReferenceMerge.bottomFace.toOrderHom
      (SimplexGrid.index 4 2 (Fin.castAdd 2 i, 0))) =
      binaryColumnNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
        (laurentComposite P u v)
        (laurentPlus P a) (polynomialProjection P a) (bottom_reference_eq P u v) i := by
  rw [BoundedFlatCoefficientBassReferenceMerge.bottom_nodes]
  change BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v
    (Fin.natAdd 36 (SimplexGrid.index 4 2 (Fin.castAdd 2 i, 0))) = _
  unfold BoundedFlatCoefficientBassBottomCommonFamily.nodes
  rw [Fin.addCases_right]
  unfold BoundedFlatCoefficientBassBottomCommonFamily.bottomNodes CommonReferenceProduct.vertices
    CommonReferenceProduct.references
  rw [SimplexGrid.decode_index]
  dsimp only
  rw [projection_plus_nodes P (a := a) i]
  have hf : ((binaryNodes (laurentPlus P a) (polynomialProjection P a) i).1 ≫
      BoundedFlatCoefficientBassLaurentBottomFace.vertices P u v 0).hom.toFunctor =
    (binaryColumnNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (laurentComposite P u v)
      (laurentPlus P a) (polynomialProjection P a)
      (bottom_reference_eq P u v) i).1.hom.toFunctor := rfl
  apply ModelSimplex.reference_node_eq hf
  simp only [eqToHom_refl, Category.comp_id]
  apply congrArg Iso.hom
  change BoundedFlatCoefficientBassBottomCommonFamily.referenceIso P u v ≪≫
    (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
      ((binaryNodes (laurentPlus P a) (polynomialProjection P a) i).2.prod
        (Iso.refl (BoundedFlatCoefficientBassLaurentBottomFace.source P u v).hom.toFunctor)) =
      (eqToIso (bottom_reference_eq P u v) ≪≫ BoundedFlatPerfectBinarySimplex.total
        (laurentComposite P u v) (laurentPlus P a ≫ polynomialProjection P a)) ≪≫
          isoWhiskerRight (binaryNodes (laurentPlus P a) (polynomialProjection P a) i).2
            (normalizedMap (laurentComposite P u v)).hom.toFunctor
  rw [composition_pair_refl, bottom_anchor_iso]; rfl

/-- All three positive source-edge nodes agree, including the original raw intermediate. -/
theorem positive_source_nodes (i : Fin 3) :
    nodes P u v (BoundedFlatCoefficientBassH0Diagram.plusFace.toOrderHom (rectangleLeftIndex i)) =
      BoundedFlatCoefficientBassReferenceMerge.nodes P u v
        (BoundedFlatCoefficientBassReferenceMerge.bottomFace.toOrderHom
        (SimplexGrid.index 4 2 (Fin.castAdd 2 i, 0))) := by
  rw [plus_source_column, bottom_plus_column]
  exact binaryColumnNode_congr _ _ _ _ _ (laurent_composite P u v) _ i

/-- Full shared normalized endpoint (H0 index 11, old merged index 21). -/
theorem shared_positive_target_node : nodes P u v 11 =
    BoundedFlatCoefficientBassReferenceMerge.nodes P u v 21 :=
  positive_source_nodes P u v 2

/-- A genuine scheme equality transports the original binary normalization reference canonically. -/
theorem binary_anchor_change {X Y Z : Scheme.{u}}
    (F : asSmallCategory (W Z) ⟶ asSmallCategory (W X))
    (f : X ⟶ Y) {g g' : Y ⟶ Z} (hg : g = g')
    (e : F.hom.toFunctor = (BoundedFlatPerfectBinarySimplex.sourceMap f g).hom.toFunctor)
    (e' : F.hom.toFunctor = (BoundedFlatPerfectBinarySimplex.sourceMap f g').hom.toFunctor) :
    (eqToIso e ≪≫ BoundedFlatPerfectBinarySimplex.total f g) ≪≫
      isoWhiskerRight (eqToIso (congrArg (fun k ↦ (normalizedMap k).hom.toFunctor) hg))
        (normalizedMap f).hom.toFunctor =
      eqToIso e' ≪≫ BoundedFlatPerfectBinarySimplex.total f g' := by
  subst g'
  rw [eqToIso_refl, isoWhiskerRight_refl]
  exact Iso.trans_refl _


/-- The actual inverse projection total equals the fixed old common total. -/
theorem bottom_minus_reference_eq
  : (BoundedFlatCoefficientBassOverlap.commonReference P u v).hom.toFunctor =
    (BoundedFlatPerfectTripleSimplex.source (laurentComposite P u v)
      (laurentMinus P a) (polynomialProjection P a)).hom.toFunctor :=
  (bottom_reference_eq P u v).trans
    (congrArg (fun k ↦ (BoundedFlatPerfectBinarySimplex.sourceMap
        (laurentComposite P u v) k).hom.toFunctor)
      ((laurentPlus_projection P a).trans (laurentMinus_projection P a).symm))

/-- The old positive-to-inverse source iso is exactly the canonical transported bottom anchor. -/
theorem bottom_minus_anchor_iso :
    BoundedFlatCoefficientBassBottomCommonFamily.referenceIso P u v ≪≫
      isoWhiskerRight (BoundedFlatCoefficientBassProjectionPath.sourceIso P a)
        (normalizedMap (laurentComposite P u v)).hom.toFunctor =
      eqToIso (bottom_minus_reference_eq P u v) ≪≫ BoundedFlatPerfectBinarySimplex.total
        (laurentComposite P u v) (laurentMinus P a ≫ polynomialProjection P a) := by
  rw [bottom_anchor_iso]
  exact binary_anchor_change _ (laurentComposite P u v)
    ((laurentPlus_projection P a).trans (laurentMinus_projection P a).symm) _ _

/-- The two noninitial inverse binary nodes retain the original source reference transport. -/
theorem projection_minus_nodes (i : Fin 2) :
    BoundedFlatCoefficientBassProjectionPath.nodes P a (Fin.natAdd 3 i) =
      (⟨(binaryNodes (laurentMinus P a) (polynomialProjection P a) i.succ).1,
        BoundedFlatCoefficientBassProjectionPath.sourceIso P a ≪≫
          (binaryNodes (laurentMinus P a) (polynomialProjection P a) i.succ).2⟩ :
        BoundedFlatCoefficientBassProjectionPath.Node P a) := by
  fin_cases i <;> rfl

/-- Both original inverse bottom nodes agree with their canonically anchored binary column. -/
theorem bottom_minus_column (i : Fin 2) :
    BoundedFlatCoefficientBassReferenceMerge.nodes P u v
      (BoundedFlatCoefficientBassReferenceMerge.bottomFace.toOrderHom
      (SimplexGrid.index 4 2 (Fin.natAdd 3 i, 0))) =
      binaryColumnNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
        (laurentComposite P u v)
        (laurentMinus P a) (polynomialProjection P a) (bottom_minus_reference_eq P u v) i.succ := by
  rw [BoundedFlatCoefficientBassReferenceMerge.bottom_nodes]
  change BoundedFlatCoefficientBassBottomCommonFamily.nodes P u v
    (Fin.natAdd 36 (SimplexGrid.index 4 2 (Fin.natAdd 3 i, 0))) = _
  unfold BoundedFlatCoefficientBassBottomCommonFamily.nodes
  rw [Fin.addCases_right]
  unfold BoundedFlatCoefficientBassBottomCommonFamily.bottomNodes CommonReferenceProduct.vertices
    CommonReferenceProduct.references
  rw [SimplexGrid.decode_index]
  dsimp only
  rw [projection_minus_nodes P (a := a) i]
  have hf : ((binaryNodes (laurentMinus P a) (polynomialProjection P a) i.succ).1 ≫
      BoundedFlatCoefficientBassLaurentBottomFace.vertices P u v 0).hom.toFunctor =
    (binaryColumnNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (laurentComposite P u v)
      (laurentMinus P a) (polynomialProjection P a)
      (bottom_minus_reference_eq P u v) i.succ).1.hom.toFunctor := rfl
  apply ModelSimplex.reference_node_eq hf
  simp only [eqToHom_refl, Category.comp_id]
  apply congrArg Iso.hom
  change BoundedFlatCoefficientBassBottomCommonFamily.referenceIso P u v ≪≫
    (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
      ((BoundedFlatCoefficientBassProjectionPath.sourceIso P a ≪≫
          (binaryNodes (laurentMinus P a) (polynomialProjection P a) i.succ).2).prod
        (Iso.refl (normalizedMap (laurentComposite P u v)).hom.toFunctor)) =
      (eqToIso (bottom_minus_reference_eq P u v) ≪≫ BoundedFlatPerfectBinarySimplex.total
        (laurentComposite P u v) (laurentMinus P a ≫ polynomialProjection P a)) ≪≫
          isoWhiskerRight (binaryNodes (laurentMinus P a) (polynomialProjection P a) i.succ).2
            (normalizedMap (laurentComposite P u v)).hom.toFunctor
  rw [composition_pair_refl, isoWhiskerRight_trans, ← Iso.trans_assoc, bottom_minus_anchor_iso]

/-- Both inverse source-edge nodes agree fully, including the distinct raw intermediate. -/
theorem negative_source_nodes (i : Fin 2) :
    nodes P u v
      (BoundedFlatCoefficientBassH0Diagram.minusFace.toOrderHom (rectangleLeftIndex i.succ)) =
      BoundedFlatCoefficientBassReferenceMerge.nodes P u v
        (BoundedFlatCoefficientBassReferenceMerge.bottomFace.toOrderHom
        (SimplexGrid.index 4 2 (Fin.natAdd 3 i, 0))) := by
  rw [minus_source_column, bottom_minus_column]
  exact binaryColumnNode_congr _ _ _ _ _ (laurent_composite P u v) _ i.succ

/-- Full shared normalized inverse endpoint (H0 index 22, old merged index 42). -/
theorem shared_negative_target_node : nodes P u v 22 =
    BoundedFlatCoefficientBassReferenceMerge.nodes P u v 42 :=
  negative_source_nodes P u v 1

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH0Merge
