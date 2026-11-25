/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumProjectionReference
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumProjectionRectangleParameters
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumSquareFivePath
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalEvaluationNaturality
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectReferenceCoherence
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectProjectionBinaryRows
public import Colib.KTheory.Waldhausen.Iterated.ReferenceWhiskeringFamily
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNerveParameter

/-! The complete original right rows of both geometric chart normalization routes. -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open AlgebraicGeometry AlgebraicGeometry.RingedSpace Convexity
open scoped Simplicial Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectProjectionChartSquareRow

open GlobalSectionChangeIndex BoundedFlatPerfectProjectionReference ModelSimplex

private abbrev W := BoundedFlatPerfectTripleSimplex.structureOn

open BoundedFlatPerfectReferenceCoherence (smallIso smallIso_postcomp)
local notation "N" => boundedAboveFlatPerfectNormalizedPullback

private abbrev binaryNodes := @BoundedFlatPerfectProjectionBinaryRows.binaryNodes
private abbrev rightIndex := BoundedFlatPerfectProjectionBinaryRows.rightIndex

private theorem right_nodes {A B C D : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D)
    (F : asSmallCategory (W D) ⟶ asSmallCategory (W A))
    (ρ : F.hom.toFunctor ≅ (BoundedFlatPerfectTripleSimplex.source f g h).hom.toFunctor)
    (i : Fin 3) :
    (⟨BoundedFlatPerfectSplitTripleSimplex.vertices f g h (rightIndex i),
      ρ ≪≫ BoundedFlatPerfectSplitTripleSimplex.references f g h (rightIndex i)⟩ :
      CommonReferenceNerve.Node F) =
    preReferenceNode F (evaluationRawMap h) (ρ ≪≫ BoundedFlatPerfectTripleSimplex.rightFirst f g h)
      (binaryNodes f g i) :=
  BoundedFlatPerfectProjectionBinaryRows.triple_right_row F f g h ρ i

variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)
  (r : C ⟶ A) (hr : q ≫ p = r)

/-- The actual ordered chart row recovers both normalization routes. -/
def chartRow : Fin 5 → Fin 18 := ![9, 10, 11, 12, 13]

/-- The complete original projection and right binary reference. -/
def chartAnchor : (reference c r).hom.toFunctor ≅
    (evaluationRawMap p ≫ BoundedFlatPerfectNativeSquareFiveSimplex.source c q).hom.toFunctor :=
  eqToIso (anchor p q c r hr) ≪≫ BoundedFlatPerfectTripleSimplex.rightFirst c q p

/-- The original projection reference transported to the middle triple. -/
def middleRef : (reference c r).hom.toFunctor ≅
    (BoundedFlatPerfectTripleSimplex.source q' b p).hom.toFunctor :=
  eqToIso (anchor p q c r hr) ≪≫
    BoundedFlatPerfectDoubleSquareCommonSimplex.middleSourceIso p q q' b c hq

private theorem chart_first_nodes (i : Fin 3) :
    nodes p q p' q' a b c hp hq r hr
      (chartRow (BoundedFlatPerfectNativeSquareFiveSimplex.firstFace.toOrderHom i)) =
      preReferenceNode (reference c r) (evaluationRawMap p)
        (chartAnchor p q c r hr) (binaryNodes c q i) := by
  have hi : chartRow (BoundedFlatPerfectNativeSquareFiveSimplex.firstFace.toOrderHom i) =
      BoundedFlatPerfectDoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i) := by
    fin_cases i <;> rfl
  rw [hi]
  unfold nodes reanchorNodes
  have hn := (BoundedFlatPerfectDoubleSquareMergedSimplex.first_nodes p q p' q' a b c hp hq
    (rightIndex i)).trans
    (BoundedFlatPerfectDoubleSquareCommonSimplex.first_nodes p q p' q' a b c hp hq
      (rightIndex i))
  refine (congrArg (ModelSimplex.reanchorNode (eqToIso (anchor p q c r hr))) hn).trans ?_
  exact right_nodes c q p _ (eqToIso (anchor p q c r hr)) i

private theorem chart_second_nodes (i : Fin 3) :
    nodes p q p' q' a b c hp hq r hr
      (chartRow (BoundedFlatPerfectNativeSquareFiveSimplex.secondFace.toOrderHom i)) =
      preReferenceNode (reference c r) (evaluationRawMap p)
        (middleRef p q q' b c hq r hr ≪≫ BoundedFlatPerfectTripleSimplex.rightFirst q' b p)
        (binaryNodes q' b i) := by
  have hi : chartRow (BoundedFlatPerfectNativeSquareFiveSimplex.secondFace.toOrderHom i) =
      BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i) := by
    fin_cases i <;> rfl
  rw [hi]
  unfold nodes reanchorNodes
  have hn := (BoundedFlatPerfectDoubleSquareMergedSimplex.middle_nodes p q p' q' a b c hp hq
    (rightIndex i)).trans
    (BoundedFlatPerfectDoubleSquareCommonSimplex.middle_nodes p q p' q' a b c hp hq
      (rightIndex i))
  refine (congrArg (ModelSimplex.reanchorNode (eqToIso (anchor p q c r hr))) hn).trans ?_
  refine (ModelSimplex.reanchorNode_assoc
    (F₀ := reference c r) (F₁ := BoundedFlatPerfectTripleSimplex.source c q p)
    (F₂ := BoundedFlatPerfectTripleSimplex.source q' b p)
    (eqToIso (anchor p q c r hr))
    (BoundedFlatPerfectDoubleSquareCommonSimplex.middleSourceIso p q q' b c hq)
    ⟨BoundedFlatPerfectSplitTripleSimplex.vertices q' b p (rightIndex i),
      BoundedFlatPerfectSplitTripleSimplex.references q' b p (rightIndex i)⟩).trans ?_
  exact right_nodes q' b p _ (middleRef p q q' b c hq r hr) i

private theorem square_second_reference {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X ⟶ T) (g' : T ⟶ Z) (e : f ≫ g = f' ≫ g')
    (i : Fin 3) :
    BoundedFlatPerfectNativeSquareFiveSimplex.nodes f g f' g' e
      (BoundedFlatPerfectNativeSquareFiveSimplex.secondFace.toOrderHom i) =
    ModelSimplex.reanchorNode (BoundedFlatPerfectNativeSquareFiveSimplex.sourceIso f g f' g' e)
      (binaryNodes f' g' i) := by
  fin_cases i
  · apply ModelSimplex.reference_node_eq
      (BoundedFlatPerfectNativeSquareFiveSimplex.source_eq f g f' g' e)
    simp only [Iso.refl_hom, Category.id_comp, Fin.zero_eta, Fin.isValue, Iso.trans_hom]
    exact (Category.comp_id _).symm
  · rfl
  · rfl

section WhiskeredReference
variable {U V W T : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}}

private theorem pre_reanchor (F : U ⟶ T) (P : U ⟶ V) {H H' : V ⟶ T}
    (ρ : F.hom.toFunctor ≅ (P ≫ H).hom.toFunctor) (η : H.hom.toFunctor ≅ H'.hom.toFunctor)
    (D : CommonReferenceNerve.Node H') :
    preReferenceNode F P ρ (ModelSimplex.reanchorNode η D) =
      preReferenceNode F P (ρ ≪≫ isoWhiskerLeft P.hom.toFunctor η) D := by
  rcases D with ⟨J₀, tau⟩
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  apply congrArg Iso.hom
  change ρ ≪≫ isoWhiskerLeft P.hom.toFunctor (η ≪≫ tau) =
    (ρ ≪≫ isoWhiskerLeft P.hom.toFunctor η) ≪≫ isoWhiskerLeft P.hom.toFunctor tau
  rw [isoWhiskerLeft_trans, Iso.trans_assoc]

private theorem post_reanchor (F : U ⟶ T) (J : W ⟶ T) {H H' : U ⟶ W}
    (ρ : F.hom.toFunctor ≅ (H ≫ J).hom.toFunctor) (η : H.hom.toFunctor ≅ H'.hom.toFunctor)
    (D : CommonReferenceNerve.Node H') :
    postReferenceNode F J ρ (ModelSimplex.reanchorNode η D) =
      postReferenceNode F J (ρ ≪≫ isoWhiskerRight η J.hom.toFunctor) D := by
  rcases D with ⟨J₀, tau⟩
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  apply congrArg Iso.hom
  change ρ ≪≫ isoWhiskerRight (η ≪≫ tau) J.hom.toFunctor =
    (ρ ≪≫ isoWhiskerRight η J.hom.toFunctor) ≪≫ isoWhiskerRight tau J.hom.toFunctor
  rw [isoWhiskerRight_trans, Iso.trans_assoc]

end WhiskeredReference

private theorem square_second_nodes (i : Fin 3) :
    preReferenceNode (reference c r) (evaluationRawMap p) (chartAnchor p q c r hr)
      (BoundedFlatPerfectNativeSquareFiveSimplex.nodes c q q' b hq
        (BoundedFlatPerfectNativeSquareFiveSimplex.secondFace.toOrderHom i)) =
    preReferenceNode (reference c r) (evaluationRawMap p)
      (chartAnchor p q c r hr ≪≫ isoWhiskerLeft (evaluationRawMap p).hom.toFunctor
        (BoundedFlatPerfectNativeSquareFiveSimplex.sourceIso c q q' b hq))
      (binaryNodes q' b i) := by
  refine (congrArg (preReferenceNode (reference c r) (evaluationRawMap p)
    (chartAnchor p q c r hr)) (square_second_reference c q q' b hq i)).trans ?_
  exact pre_reanchor (reference c r) (evaluationRawMap p) (chartAnchor p q c r hr)
    (BoundedFlatPerfectNativeSquareFiveSimplex.sourceIso c q q' b hq) (binaryNodes q' b i)

/-- Every chart row node keeps its exact projection source and full natural isomorphism. -/
theorem chart_row_nodes (i : Fin 5) :
    nodes p q p' q' a b c hp hq r hr (chartRow i) =
      preReferenceNode (reference c r) (evaluationRawMap p) (chartAnchor p q c r hr)
        (BoundedFlatPerfectNativeSquareFiveSimplex.nodes c q q' b hq i) := by
  have hs (j : Fin 3) :
      nodes p q p' q' a b c hp hq r hr
        (chartRow (BoundedFlatPerfectNativeSquareFiveSimplex.secondFace.toOrderHom j)) =
      preReferenceNode (reference c r) (evaluationRawMap p) (chartAnchor p q c r hr)
        (BoundedFlatPerfectNativeSquareFiveSimplex.nodes c q q' b hq
          (BoundedFlatPerfectNativeSquareFiveSimplex.secondFace.toOrderHom j)) :=
    pre_families_match (reference c r) (evaluationRawMap p)
      (BoundedFlatPerfectBinarySimplex.sourceMap q' b) (binaryNodes q' b)
      (chart_second_nodes p q p' q' a b c hp hq r hr) (square_second_nodes p q q' b c hq r hr) 0
      (chart_first_nodes p q p' q' a b c hp hq r hr 0) j
  fin_cases i
  · exact chart_first_nodes p q p' q' a b c hp hq r hr 0
  · exact chart_first_nodes p q p' q' a b c hp hq r hr 1
  · exact chart_first_nodes p q p' q' a b c hp hq r hr 2
  · exact hs 1
  · exact hs 2

/-- The entire original reverse-forward path agrees in any embedded projection rectangle. -/
theorem chart_parameter {k : ℕ} (α : ⦋17⦌ ⟶ ⦋k⦌) (s : unitInterval) :
    StdSimplex.map (α.toOrderHom ∘ chartRow)
      (BoundedFlatPerfectNativeSquareFiveSimplex.parameter s) =
      BoundedFlatPerfectProjectionRectangleParameters.L α s := by
  let β : ⦋4⦌ ⟶ ⦋17⦌ := SimplexCategory.Hom.mk ⟨chartRow, by decide⟩
  change embed (β ≫ α) (BoundedFlatPerfectNativeSquareFiveSimplex.parameter s) = _
  unfold BoundedFlatPerfectNativeSquareFiveSimplex.parameter
  exact map_trans_values (embed (β ≫ α)) _ _ _ _
    (fun t ↦ map_binaryPath (β ≫ α) 0 1 2 (unitInterval.symm t))
    (map_binaryPath (β ≫ α) 0 3 4) s

private def leftIndex : Fin 3 → Fin 8 := ![2, 3, 7]

private theorem left_nodes {A B C D : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D)
    (F : asSmallCategory (W D) ⟶ asSmallCategory (W A))
    (ρ : F.hom.toFunctor ≅ (BoundedFlatPerfectTripleSimplex.source f g h).hom.toFunctor)
    (i : Fin 3) :
    (⟨BoundedFlatPerfectSplitTripleSimplex.vertices f g h (leftIndex i),
      ρ ≪≫ BoundedFlatPerfectSplitTripleSimplex.references f g h (leftIndex i)⟩ :
      CommonReferenceNerve.Node F) =
    postReferenceNode F (evaluationRawMap f) (H := BoundedFlatPerfectBinarySimplex.sourceMap g h)
      (ρ ≪≫ BoundedFlatPerfectBinarySimplex.total f (g ≫ h))
      (binaryNodes g h i) := by
  fin_cases i
  · apply ModelSimplex.reference_node_eq (by rfl)
    simp only [eqToHom_refl, Category.comp_id]
    change (ρ ≪≫ BoundedFlatPerfectBinarySimplex.total f (g ≫ h)).hom = _
    apply NatTrans.ext
    funext x
    simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, whiskerRight_app]
    let α := ρ ≪≫ BoundedFlatPerfectBinarySimplex.total f (g ≫ h)
    have hId := (evaluationRawMap f).hom.toFunctor.map_id
      ((BoundedFlatPerfectBinarySimplex.sourceMap g h).hom.toFunctor.obj x)
    exact ((congrArg (fun e ↦ α.hom.app x ≫ e) hId).trans
      (Category.comp_id (α.hom.app x))).symm
  · apply ModelSimplex.reference_node_eq (by rfl)
    simp only [eqToHom_refl, Category.comp_id]
    change (ρ ≪≫ (BoundedFlatPerfectBinarySimplex.total f (g ≫ h) ≪≫
      BoundedFlatPerfectSplitTripleSimplex.leftSecondGeometric f g h)).hom = _
    rw [← Iso.trans_assoc]
    rfl
  · apply ModelSimplex.reference_node_eq (by rfl)
    simp only [eqToHom_refl, Category.comp_id]
    change (ρ ≪≫ (BoundedFlatPerfectBinarySimplex.total f (g ≫ h) ≪≫
      BoundedFlatPerfectTripleSimplex.leftSecond f g h)).hom = _
    apply congrArg Iso.hom
    have hA : Functor.associator (N h) (N g) (N f) = Iso.refl _ := rfl
    have hSecond : BoundedFlatPerfectTripleSimplex.leftSecond f g h =
        isoWhiskerRight (BoundedFlatPerfectBinarySimplex.total g h)
          (evaluationRawMap f).hom.toFunctor := by
      change smallIso (isoWhiskerRight (boundedAboveFlatPerfectNormalizedPullbackCompIso g h)
        (N f) ≪≫ Functor.associator (N h) (N g) (N f)) =
        isoWhiskerRight (smallIso (boundedAboveFlatPerfectNormalizedPullbackCompIso g h))
          (AsSmall.down ⋙ N f ⋙ AsSmall.up)
      rw [hA, Iso.trans_refl, ← smallIso_postcomp]
    exact (Iso.trans_assoc _ _ _).symm.trans
      (congrArg (fun e ↦ (ρ ≪≫ BoundedFlatPerfectBinarySimplex.total f (g ≫ h)) ≪≫ e) hSecond)

/-- The five original polynomial nodes, whose two ordered rows share node thirteen. -/
def polynomialRow : Fin 5 → Fin 18 := ![5, 6, 13, 7, 17]

/-- The entire original reference for the polynomial square followed by its raw chart. -/
def polynomialAnchor : (reference c r).hom.toFunctor ≅
    (BoundedFlatPerfectNativeSquareFiveSimplex.source b p ≫ evaluationRawMap q').hom.toFunctor :=
  middleRef p q q' b c hq r hr ≪≫ BoundedFlatPerfectBinarySimplex.total q' (b ≫ p)

private def lastRef : (reference c r).hom.toFunctor ≅
    (BoundedFlatPerfectTripleSimplex.source q' p' a).hom.toFunctor :=
  eqToIso (anchor p q c r hr) ≪≫
    BoundedFlatPerfectDoubleSquareCommonSimplex.lastSourceIso p q p' q' a b c hp hq

private theorem polynomial_first_nodes (i : Fin 3) :
    nodes p q p' q' a b c hp hq r hr
      (polynomialRow (BoundedFlatPerfectNativeSquareFiveSimplex.firstFace.toOrderHom i)) =
      postReferenceNode (reference c r) (evaluationRawMap q')
        (polynomialAnchor p q q' b c hq r hr) (binaryNodes b p i) := by
  have hi : polynomialRow (BoundedFlatPerfectNativeSquareFiveSimplex.firstFace.toOrderHom i) =
      BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace.toOrderHom (leftIndex i) := by
    fin_cases i <;> rfl
  rw [hi]
  unfold nodes reanchorNodes
  have hn := (BoundedFlatPerfectDoubleSquareMergedSimplex.middle_nodes p q p' q' a b c hp hq
    (leftIndex i)).trans
    (BoundedFlatPerfectDoubleSquareCommonSimplex.middle_nodes p q p' q' a b c hp hq
      (leftIndex i))
  refine (congrArg (ModelSimplex.reanchorNode (eqToIso (anchor p q c r hr))) hn).trans ?_
  refine (ModelSimplex.reanchorNode_assoc
    (F₀ := reference c r) (F₁ := BoundedFlatPerfectTripleSimplex.source c q p)
    (F₂ := BoundedFlatPerfectTripleSimplex.source q' b p)
    (eqToIso (anchor p q c r hr))
    (BoundedFlatPerfectDoubleSquareCommonSimplex.middleSourceIso p q q' b c hq)
    ⟨BoundedFlatPerfectSplitTripleSimplex.vertices q' b p (leftIndex i),
      BoundedFlatPerfectSplitTripleSimplex.references q' b p (leftIndex i)⟩).trans ?_
  exact left_nodes q' b p _ (middleRef p q q' b c hq r hr) i

private theorem polynomial_second_nodes (i : Fin 3) :
    nodes p q p' q' a b c hp hq r hr
      (polynomialRow (BoundedFlatPerfectNativeSquareFiveSimplex.secondFace.toOrderHom i)) =
      postReferenceNode (reference c r) (evaluationRawMap q')
        (H := BoundedFlatPerfectBinarySimplex.sourceMap p' a)
        (lastRef p q p' q' a b c hp hq r hr ≪≫ BoundedFlatPerfectBinarySimplex.total q' (p' ≫ a))
        (binaryNodes p' a i) := by
  have hi : polynomialRow (BoundedFlatPerfectNativeSquareFiveSimplex.secondFace.toOrderHom i) =
      BoundedFlatPerfectDoubleSquareMergedSimplex.lastFace.toOrderHom (leftIndex i) := by
    fin_cases i <;> rfl
  rw [hi]
  unfold nodes reanchorNodes
  have hn := (BoundedFlatPerfectDoubleSquareMergedSimplex.last_nodes p q p' q' a b c hp hq
    (leftIndex i)).trans
    (BoundedFlatPerfectDoubleSquareCommonSimplex.last_nodes p q p' q' a b c hp hq
      (leftIndex i))
  refine (congrArg (ModelSimplex.reanchorNode (eqToIso (anchor p q c r hr))) hn).trans ?_
  refine (ModelSimplex.reanchorNode_assoc
    (F₀ := reference c r) (F₁ := BoundedFlatPerfectTripleSimplex.source c q p)
    (F₂ := BoundedFlatPerfectTripleSimplex.source q' p' a)
    (eqToIso (anchor p q c r hr))
    (BoundedFlatPerfectDoubleSquareCommonSimplex.lastSourceIso p q p' q' a b c hp hq)
    ⟨BoundedFlatPerfectSplitTripleSimplex.vertices q' p' a (leftIndex i),
      BoundedFlatPerfectSplitTripleSimplex.references q' p' a (leftIndex i)⟩).trans ?_
  exact left_nodes q' p' a _ (lastRef p q p' q' a b c hp hq r hr) i

private theorem square_second_post_nodes (i : Fin 3) :
    postReferenceNode (reference c r) (evaluationRawMap q') (polynomialAnchor p q q' b c hq r hr)
      (BoundedFlatPerfectNativeSquareFiveSimplex.nodes b p p' a hp
        (BoundedFlatPerfectNativeSquareFiveSimplex.secondFace.toOrderHom i)) =
    postReferenceNode (reference c r) (evaluationRawMap q')
      (polynomialAnchor p q q' b c hq r hr ≪≫
        isoWhiskerRight (BoundedFlatPerfectNativeSquareFiveSimplex.sourceIso b p p' a hp)
          (evaluationRawMap q').hom.toFunctor) (binaryNodes p' a i) := by
  refine (congrArg (postReferenceNode (reference c r) (evaluationRawMap q')
    (polynomialAnchor p q q' b c hq r hr)) (square_second_reference b p p' a hp i)).trans ?_
  exact post_reanchor (reference c r) (evaluationRawMap q') (polynomialAnchor p q q' b c hq r hr)
    (BoundedFlatPerfectNativeSquareFiveSimplex.sourceIso b p p' a hp) (binaryNodes p' a i)

/-- Each raw polynomial node keeps its full original reference after postcomposition. -/
theorem polynomial_row_nodes (i : Fin 5) :
    nodes p q p' q' a b c hp hq r hr (polynomialRow i) =
      postReferenceNode (reference c r) (evaluationRawMap q')
        (polynomialAnchor p q q' b c hq r hr)
        (BoundedFlatPerfectNativeSquareFiveSimplex.nodes b p p' a hp i) := by
  have hs (j : Fin 3) :
      nodes p q p' q' a b c hp hq r hr
        (polynomialRow (BoundedFlatPerfectNativeSquareFiveSimplex.secondFace.toOrderHom j)) =
      postReferenceNode (reference c r) (evaluationRawMap q')
        (polynomialAnchor p q q' b c hq r hr)
        (BoundedFlatPerfectNativeSquareFiveSimplex.nodes b p p' a hp
          (BoundedFlatPerfectNativeSquareFiveSimplex.secondFace.toOrderHom j)) :=
    post_families_match (reference c r) (evaluationRawMap q')
      (BoundedFlatPerfectBinarySimplex.sourceMap p' a) (binaryNodes p' a)
      (polynomial_second_nodes p q p' q' a b c hp hq r hr)
      (square_second_post_nodes p q p' q' a b c hp hq r hr) 0
      (polynomial_first_nodes p q p' q' a b c hp hq r hr 0) j
  fin_cases i
  · exact polynomial_first_nodes p q p' q' a b c hp hq r hr 0
  · exact polynomial_first_nodes p q p' q' a b c hp hq r hr 1
  · exact polynomial_first_nodes p q p' q' a b c hp hq r hr 2
  · exact hs 1
  · exact hs 2

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectProjectionChartSquareRow
