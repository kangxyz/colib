/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectProjectionBinaryRows

/-!
# The first two right binary rows of an actual Bass projection rectangle

Both row representations retain the actual transported source, intermediate
and normalized target. Adapted from `ProjectionRightRows.lean` in Quillen at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open CategoryTheory.Waldhausen.IteratedS

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectProjectionBinaryRows

open ModelSimplex
local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn

variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)
  (r : C ⟶ A) (hr : q ≫ p = r)
  (F : asSmallCategory (W A) ⟶ asSmallCategory (W C'))
  (e : F.hom.toFunctor = (BoundedFlatPerfectProjectionReference.reference c r).hom.toFunctor)

/--
An original projection-rectangle node reanchored from the projection reference to `F` through
the equality `e`.
-/
def projectionNativeNode (i : Fin 18) :=
  ModelSimplex.reanchorNodes (F₀ := F)
    (F₁ := BoundedFlatPerfectProjectionReference.reference c r) (eqToIso e)
    (BoundedFlatPerfectProjectionReference.nodes p q p' q' a b c hp hq r hr) i

/--
The reference from `F` to the first triple `c, q, p`, combining `e` with the projection equation
`hr`.
-/
def projectionFirstReference :
    F.hom.toFunctor ≅ (BoundedFlatPerfectTripleSimplex.source c q p).hom.toFunctor :=
  eqToIso e ≪≫ eqToIso (BoundedFlatPerfectProjectionReference.anchor p q c r hr)

/--
The reference from `F` to the middle triple `q', b, p`, extending the first-triple reference by
the middle-square isomorphism.
-/
def projectionMiddleReference :
    F.hom.toFunctor ≅ (BoundedFlatPerfectTripleSimplex.source q' b p).hom.toFunctor :=
  projectionFirstReference p q c r hr F e ≪≫
    BoundedFlatPerfectDoubleSquareCommonSimplex.middleSourceIso p q q' b c hq

/-- Reanchor the actual projection rectangle by composing its two reference isomorphisms. -/
theorem projection_native_anchor (i : Fin 18) :
    projectionNativeNode p q p' q' a b c hp hq r hr F e i =
      reanchorNode (F₀ := F) (F₁ := BoundedFlatPerfectTripleSimplex.source c q p)
        (projectionFirstReference p q c r hr F e)
        (BoundedFlatPerfectDoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq i) :=
  reanchorNode_assoc (F₀ := F) (F₁ := BoundedFlatPerfectProjectionReference.reference c r)
    (F₂ := BoundedFlatPerfectTripleSimplex.source c q p)
    (eqToIso e) (eqToIso (BoundedFlatPerfectProjectionReference.anchor p q c r hr))
    (BoundedFlatPerfectDoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq i)

/-- Every full first-triple node is unchanged after its two actual reference transports. -/
theorem projection_first_nodes (i : Fin 8) :
    projectionNativeNode p q p' q' a b c hp hq r hr F e
      (BoundedFlatPerfectDoubleSquareMergedSimplex.firstFace.toOrderHom i) =
    (⟨BoundedFlatPerfectSplitTripleSimplex.vertices c q p i,
      projectionFirstReference p q c r hr F e ≪≫
        BoundedFlatPerfectSplitTripleSimplex.references c q p i⟩ :
      Σ G : asSmallCategory (W A) ⟶ asSmallCategory (W C'),
        F.hom.toFunctor ≅ G.hom.toFunctor) := by
  refine (projection_native_anchor p q p' q' a b c hp hq r hr F e _).trans ?_
  exact reanchorNode_congr (F₀ := F) (F₁ := BoundedFlatPerfectTripleSimplex.source c q p)
    (projectionFirstReference p q c r hr F e)
    ((BoundedFlatPerfectDoubleSquareMergedSimplex.first_nodes p q p' q' a b c hp hq i).trans
      (BoundedFlatPerfectDoubleSquareCommonSimplex.first_nodes p q p' q' a b c hp hq i))

/-- Every full middle-triple node retains the original actual square-naturality source iso. -/
theorem projection_middle_nodes (i : Fin 8) :
    projectionNativeNode p q p' q' a b c hp hq r hr F e
      (BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace.toOrderHom i) =
    (⟨BoundedFlatPerfectSplitTripleSimplex.vertices q' b p i,
      projectionMiddleReference p q q' b c hq r hr F e ≪≫
        BoundedFlatPerfectSplitTripleSimplex.references q' b p i⟩ :
      Σ G : asSmallCategory (W A) ⟶ asSmallCategory (W C'),
        F.hom.toFunctor ≅ G.hom.toFunctor) := by
  refine (projection_native_anchor p q p' q' a b c hp hq r hr F e _).trans ?_
  have hn := reanchorNode_congr (F₀ := F) (F₁ := BoundedFlatPerfectTripleSimplex.source c q p)
    (projectionFirstReference p q c r hr F e)
    ((BoundedFlatPerfectDoubleSquareMergedSimplex.middle_nodes p q p' q' a b c hp hq i).trans
      (BoundedFlatPerfectDoubleSquareCommonSimplex.middle_nodes p q p' q' a b c hp hq i))
  exact hn.trans (reanchorNode_assoc (F₀ := F) (F₁ := BoundedFlatPerfectTripleSimplex.source c q p)
    (F₂ := BoundedFlatPerfectTripleSimplex.source q' b p)
    (projectionFirstReference p q c r hr F e)
    (BoundedFlatPerfectDoubleSquareCommonSimplex.middleSourceIso p q q' b c hq)
    ⟨BoundedFlatPerfectSplitTripleSimplex.vertices q' b p i,
      BoundedFlatPerfectSplitTripleSimplex.references q' b p i⟩)

/-- The first original right row is exactly its precomposed native binary normalization. -/
theorem projection_first_right_row (i : Fin 3) :
    projectionNativeNode p q p' q' a b c hp hq r hr F e
      (BoundedFlatPerfectDoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i)) =
      preBinaryNodes F (normalizedMap p) c q
        (rightRowReference F c q p (projectionFirstReference p q c r hr F e)) i :=
  (projection_first_nodes p q p' q' a b c hp hq r hr F e (rightIndex i)).trans
    (triple_right_row F c q p (projectionFirstReference p q c r hr F e) i)

/-- The actual middle right row retains the native square equality before binary normalization. -/
theorem projection_middle_right_row (i : Fin 3) :
    projectionNativeNode p q p' q' a b c hp hq r hr F e
      (BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i)) =
      preBinaryNodes F (normalizedMap p) q' b
        (rightRowReference F q' b p (projectionMiddleReference p q q' b c hq r hr F e)) i :=
  (projection_middle_nodes p q p' q' a b c hp hq r hr F e (rightIndex i)).trans
    (triple_right_row F q' b p (projectionMiddleReference p q q' b c hq r hr F e) i)

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectProjectionBinaryRows
