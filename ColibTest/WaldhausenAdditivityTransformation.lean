/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.CategoryTheory.Waldhausen.Additivity.MixedTransformation

/-! Source-only regressions for actual maps, quotient-first endpoints, two
independent restrictions and all-cut zero diagrams. Compilation is pending. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Additivity
open SSet.MixedOrdinalCylinder
open scoped Simplicial
universe u v
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (V : Structure C) (W : Structure D) {F G H F' G' H' : C ⥤ D}
  (a : F ⟶ G) (a' : F' ⟶ G') (b : G ⟶ H) (b' : G' ⟶ H')
  (hs : IsCofibrationSequence V W a b) (hs' : IsCofibrationSequence V W a' b')
  (ηF : F ⟶ F') (ηG : G ⟶ G') (haη : a ≫ ηG = ηF ≫ a')

-- The entire transformation is the unchanged conjugate, not just equal endpoints.
example : normalizedPushoutTransformation W a a' ηF ηG haη b b' V hs hs' =
    (normalizedPushoutIso V W a hs.exactF hs.exactG hs.cofibration).inv ≫
      pushoutTransformation W a a' hs.cofibration.app_cof hs'.cofibration.app_cof
        ηF ηG haη ≫
      (normalizedPushoutIso V W a' hs'.exactF hs'.exactG hs'.cofibration).hom := rfl

-- The original gluing hypotheses suffice for every actual arrow.
example (hηF : ∀ X, W.weq (ηF.app X)) (hηG : ∀ X, W.weq (ηG.app X))
    (f : Arrow C) :
    W.weq ((normalizedPushoutTransformation W a a' ηF ηG haη b b' V hs hs').app f) :=
  normalizedPushoutTransformation_weak W a a' ηF ηG haη b b' V hs hs' hηF hηG f

-- Distinct interval and nerve restrictions keep each actual component.
example {n n' m m' : SimplexCategory} (μ : n' ⟶ n) (ν : m' ⟶ m)
    (φ : Cut n) (A : Grid₂ (mixedOrdinal φ) m ⥤ C) (x : Grid₂ n' m') :
    HEq ((normalizedMixedTransformation V W a a' b b' hs hs' ηF ηG haη φ A).app
        ((gridMap₂ μ ν).obj x))
      ((normalizedMixedTransformation V W a a' b b' hs hs' ηF ηG haη (μ ≫ φ)
        (gridMap₂ (mixedMap μ (fun _ ↦ le_rfl)) ν ⋙ A)).app x) :=
  normalizedMixedTransformation_reindex V W a a' b b' hs hs' ηF ηG haη μ ν φ A x

-- The full cylinder is the constant chosen-zero diagram at every cut and nerve time.
example {n m : SimplexCategory} (φ : Cut n) (τ : m ⟶ ⦋1⦌) :
    nerveCylinderDiagram
        (normalizedMixedTransformation V W a a' b b' hs hs' ηF ηG haη φ
          ((Functor.const (Grid₂ (mixedOrdinal φ) m)).obj V.zero)) τ =
      (Functor.const (Grid₂ n m)).obj W.zero :=
  normalizedMixedTransformation_nerveCylinder_zero V W a a' b b' hs hs' ηF ηG haη φ τ

variable [HasBinaryCoproducts D] (ηH : H ⟶ H') (hbη : b ≫ ηH = ηG ≫ b')

-- Coproduct order is literally quotient first and subobject second.
example (X : C × C) : (splitEndpointTransformation ηF ηH).app X =
    coprod.map (ηH.app X.1) (ηF.app X.2) := rfl

-- The entire separated endpoint square commutes before realization.
example (n m : SimplexCategoryᵒᵖ)
    (A : ((SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V).obj n).obj m) :
    Functor.whiskerLeft
        (intervalArrows (SSet.OrdinalJoin.left n.unop n.unop)
          (SSet.OrdinalJoin.right n.unop n.unop) (left_le_right n.unop) A.1)
        (normalizedPushoutTransformation W a a' ηF ηG haη b b' V hs hs') ≫
        normalizedSeparatedEndpointFamily V W a' b' hs' n m A =
      normalizedSeparatedEndpointFamily V W a b hs n m A ≫
        Functor.whiskerLeft (separatedPairGrid A.1)
          (normalizedSplitEndpointTransformation W a a' ηF b b' ηH V hs hs') :=
  normalizedPushoutTransformation_separatedEndpointFamily W a a' ηF ηG haη
    b b' ηH hbη V hs hs' n m A
