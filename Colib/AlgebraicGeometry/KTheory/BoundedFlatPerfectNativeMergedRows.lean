/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectProjectionBinaryRows
public import Colib.KTheory.Waldhausen.Iterated.ReferenceWhiskeringFamily

/-!
# Full native binary rows of the merged composition rectangle

The original first/middle right rows retain all dependent references under precomposition.
The middle/last left columns retain the actual square-reference paths under postcomposition.

Adapted from `NativeMergedColumns.lean` and `NativeMergedRightRows.lean` in
`Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor CategoryTheory.Waldhausen AlgebraicGeometry
open CategoryTheory.Waldhausen.IteratedS (asSmallCategory)
open CategoryTheory.Waldhausen.IteratedS.ModelSimplex
open scoped Simplicial
universe u
namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectNativeMergedRows

open BoundedFlatPerfectProjectionBinaryRows

/-- The original left column inside a split triple. -/
def leftIndex : Fin 3 → Fin 8 := ![2, 3, 7]

theorem triple_left_column_iso {X Y Z T : Scheme.{u}}
    (F : asSmallCategory (BoundedFlatPerfectTripleSimplex.structureOn T) ⟶
      asSmallCategory (BoundedFlatPerfectTripleSimplex.structureOn X))
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    (ρ : F.hom.toFunctor ≅ (BoundedFlatPerfectTripleSimplex.source f g h).hom.toFunctor)
    (i : Fin 3) :
    (⟨BoundedFlatPerfectSplitTripleSimplex.vertices f g h (leftIndex i),
      ρ ≪≫ BoundedFlatPerfectSplitTripleSimplex.references f g h (leftIndex i)⟩ :
      Σ G : asSmallCategory (BoundedFlatPerfectTripleSimplex.structureOn T) ⟶
        asSmallCategory (BoundedFlatPerfectTripleSimplex.structureOn X),
        F.hom.toFunctor ≅ G.hom.toFunctor) =
      postReferenceNode F (normalizedMap f)
        (H := BoundedFlatPerfectBinarySimplex.sourceMap g h)
        (ρ ≪≫ BoundedFlatPerfectBinarySimplex.total f (g ≫ h)) (binaryNodes g h i) := by
  let S := BoundedFlatPerfectTripleSimplex.source f g h
  let changeRef (N : Σ G : asSmallCategory (BoundedFlatPerfectTripleSimplex.structureOn T) ⟶
      asSmallCategory (BoundedFlatPerfectTripleSimplex.structureOn X),
      S.hom.toFunctor ≅ G.hom.toFunctor) :=
    (⟨N.1, ρ ≪≫ N.2⟩ :
      Σ G : asSmallCategory (BoundedFlatPerfectTripleSimplex.structureOn T) ⟶
        asSmallCategory (BoundedFlatPerfectTripleSimplex.structureOn X),
        F.hom.toFunctor ≅ G.hom.toFunctor)
  simpa only [changeRef, leftIndex, tripleLeftNode, binaryColumnNode, postReferenceNode,
    eqToIso_refl, Iso.refl_trans, Iso.trans_assoc] using
      congrArg changeRef (triple_left_column S f g h rfl i)

variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)

/-- Every middle-triple node retains the original whole-square source reference. -/
theorem merged_middle_nodes (i : Fin 8) :
    BoundedFlatPerfectDoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq
      (BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace.toOrderHom i) =
    (⟨BoundedFlatPerfectSplitTripleSimplex.vertices q' b p i,
      BoundedFlatPerfectDoubleSquareCommonSimplex.middleSourceIso p q q' b c hq ≪≫
        BoundedFlatPerfectSplitTripleSimplex.references q' b p i⟩ :
          BoundedFlatPerfectDoubleSquareCommonSimplex.Node p q c) :=
  (BoundedFlatPerfectDoubleSquareMergedSimplex.middle_nodes p q p' q' a b c hp hq i).trans
    (BoundedFlatPerfectDoubleSquareCommonSimplex.middle_nodes p q p' q' a b c hp hq i)

/-- Every last-triple node retains the actual total-square source equality. -/
theorem merged_last_nodes (i : Fin 8) :
    BoundedFlatPerfectDoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq
      (BoundedFlatPerfectDoubleSquareMergedSimplex.lastFace.toOrderHom i) =
    (⟨BoundedFlatPerfectSplitTripleSimplex.vertices q' p' a i,
      BoundedFlatPerfectDoubleSquareCommonSimplex.lastSourceIso p q p' q' a b c hp hq ≪≫
        BoundedFlatPerfectSplitTripleSimplex.references q' p' a i⟩ :
          BoundedFlatPerfectDoubleSquareCommonSimplex.Node p q c) :=
  (BoundedFlatPerfectDoubleSquareMergedSimplex.last_nodes p q p' q' a b c hp hq i).trans
    (BoundedFlatPerfectDoubleSquareCommonSimplex.last_nodes p q p' q' a b c hp hq i)

/-- The entire original middle binary column is its native binary family postcomposed by q'. -/
theorem merged_middle_column (i : Fin 3) :
    BoundedFlatPerfectDoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq
      (BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace.toOrderHom (leftIndex i)) =
    postReferenceNode (BoundedFlatPerfectTripleSimplex.source c q p) (normalizedMap q')
      (H := BoundedFlatPerfectBinarySimplex.sourceMap b p)
      (BoundedFlatPerfectDoubleSquareCommonSimplex.middleSourceIso p q q' b c hq ≪≫
        BoundedFlatPerfectBinarySimplex.total q' (b ≫ p)) (binaryNodes b p i) :=
  (merged_middle_nodes p q p' q' a b c hp hq (leftIndex i)).trans
    (triple_left_column_iso (BoundedFlatPerfectTripleSimplex.source c q p) q' b p
      (BoundedFlatPerfectDoubleSquareCommonSimplex.middleSourceIso p q q' b c hq) i)

/-- The entire last column retains the original total equality before both binary pieces. -/
theorem merged_last_column (i : Fin 3) :
    BoundedFlatPerfectDoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq
      (BoundedFlatPerfectDoubleSquareMergedSimplex.lastFace.toOrderHom (leftIndex i)) =
    postReferenceNode (BoundedFlatPerfectTripleSimplex.source c q p) (normalizedMap q')
      (H := BoundedFlatPerfectBinarySimplex.sourceMap p' a)
      (BoundedFlatPerfectDoubleSquareCommonSimplex.lastSourceIso p q p' q' a b c hp hq ≪≫
        BoundedFlatPerfectBinarySimplex.total q' (p' ≫ a)) (binaryNodes p' a i) :=
  (merged_last_nodes p q p' q' a b c hp hq (leftIndex i)).trans
    (triple_left_column_iso (BoundedFlatPerfectTripleSimplex.source c q p) q' p' a
      (BoundedFlatPerfectDoubleSquareCommonSimplex.lastSourceIso p q p' q' a b c hp hq) i)

/-- The first right row retains the original first-triple reference, before any chart projection. -/
theorem merged_first_right_row (i : Fin 3) :
    BoundedFlatPerfectDoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq
      (BoundedFlatPerfectDoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i)) =
    preReferenceNode (BoundedFlatPerfectTripleSimplex.source c q p) (normalizedMap p)
      (rightRowReference (BoundedFlatPerfectTripleSimplex.source c q p) c q p (Iso.refl _))
      (binaryNodes c q i) := by
  have hn := (BoundedFlatPerfectDoubleSquareMergedSimplex.first_nodes p q p' q' a b c hp hq
    (rightIndex i)).trans
    (BoundedFlatPerfectDoubleSquareCommonSimplex.first_nodes p q p' q' a b c hp hq (rightIndex i))
  refine hn.trans ?_
  simpa only [tripleRightNode, Iso.refl_trans, preBinaryNodes, preReferenceNode] using
    triple_right_row (BoundedFlatPerfectTripleSimplex.source c q p) c q p (Iso.refl _) i

/-- The second right row retains its actual middle-square source equality. -/
theorem merged_middle_right_row (i : Fin 3) :
    BoundedFlatPerfectDoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq
      (BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i)) =
    preReferenceNode (BoundedFlatPerfectTripleSimplex.source c q p) (normalizedMap p)
      (rightRowReference (BoundedFlatPerfectTripleSimplex.source c q p) q' b p
        (BoundedFlatPerfectDoubleSquareCommonSimplex.middleSourceIso p q q' b c hq))
      (binaryNodes q' b i) :=
  (merged_middle_nodes p q p' q' a b c hp hq (rightIndex i)).trans
    (triple_right_row (BoundedFlatPerfectTripleSimplex.source c q p) q' b p
      (BoundedFlatPerfectDoubleSquareCommonSimplex.middleSourceIso p q q' b c hq) i)

/-- The first left column is the original binary family postcomposed by the first chart map. -/
theorem merged_first_left_column (i : Fin 3) :
    BoundedFlatPerfectDoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq
      (BoundedFlatPerfectDoubleSquareMergedSimplex.firstFace.toOrderHom (leftIndex i)) =
    postReferenceNode (BoundedFlatPerfectTripleSimplex.source c q p) (normalizedMap c)
      (H := BoundedFlatPerfectBinarySimplex.sourceMap q p)
      (BoundedFlatPerfectBinarySimplex.total c (q ≫ p)) (binaryNodes q p i) := by
  have h : BoundedFlatPerfectDoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq
      (BoundedFlatPerfectDoubleSquareMergedSimplex.firstFace.toOrderHom (leftIndex i)) =
      tripleLeftNode (BoundedFlatPerfectTripleSimplex.source c q p) c q p rfl i := by
    fin_cases i <;> rfl
  exact h.trans (triple_left_column (BoundedFlatPerfectTripleSimplex.source c q p) c q p rfl i)

/-- The last right row retains the full total-square source of the target binary family. -/
theorem merged_last_right_row (i : Fin 3) :
    BoundedFlatPerfectDoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq
      (BoundedFlatPerfectDoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i)) =
    preReferenceNode (BoundedFlatPerfectTripleSimplex.source c q p) (normalizedMap a)
      (rightRowReference (BoundedFlatPerfectTripleSimplex.source c q p) q' p' a
        (BoundedFlatPerfectDoubleSquareCommonSimplex.lastSourceIso p q p' q' a b c hp hq))
      (binaryNodes q' p' i) :=
  (merged_last_nodes p q p' q' a b c hp hq (rightIndex i)).trans
    (triple_right_row (BoundedFlatPerfectTripleSimplex.source c q p) q' p' a
      (BoundedFlatPerfectDoubleSquareCommonSimplex.lastSourceIso p q p' q' a b c hp hq) i)

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectNativeMergedRows
