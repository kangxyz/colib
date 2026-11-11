/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Waldhausen.Iterated.RowTransformationSpectrum

/-! Consumers retain both cell intervals and the separate degree-zero loop coordinate. -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor MonoidalCategory Topology
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open scoped Simplicial Topology unitInterval
universe u
variable {V W : WideSubcategory preservesZero.{u}} {F G : V ⟶ W}
  (η : F.hom.toFunctor ⟶ G.hom.toFunctor) (hη : ∀ A, W.obj.waldhausen.weq (η.app A))

example (k : ℕ) (n : SimplexCategoryᵒᵖ) (A : ((stages k).obj V).obj n)
    (τ θ : (Δ[1]).obj n) :
    rowTransformationSimplex η hη k n A τ θ =
      (stageCylinder k W).app n (stageTransformationFunction k η hη n A τ, θ) :=
  rowTransformationSimplex_eq η hη k n A τ θ

example (k : ℕ) : rowTransformationCylinder η hη k =
    (stageTransformationCylinder k η hη ▷ Δ[1]) ≫ stageCylinder k W :=
  rowTransformationCylinder_eq η hη k

example (k : ℕ) (s t : unitInterval) (x : stageSpace k V) :
    rowTransformationRealization η hη k (s, (t, x)) =
      (prespectrum W).structureMap (k + 1)
        ((prespectrumTransformationHomotopy η hη).level (k + 1) (t, x)) s :=
  rowTransformationRealization_structure η hη k s t x

example (k : ℕ) (s t : unitInterval) (x : stageSpace k V) :
    Path.toContinuousMap ((rowTransformationSpectrumHomotopy η hη).level (k + 1) (t, x)) s =
      rowTransformationRealization η hη k (s, (t, x)) :=
  rowTransformationSpectrumHomotopy_succ η hη k t s x

example (t a s : unitInterval) (γ : Path (stagePoint 0 V) (stagePoint 0 V)) :
    Path.toContinuousMap
      (Path.toContinuousMap ((rowTransformationSpectrumHomotopy η hη).level 0 (t, γ)) a) s =
      rowTransformationRealization η hη 0 (s, (t, γ a)) :=
  rowTransformationSpectrumHomotopy_zero η hη t a s γ
