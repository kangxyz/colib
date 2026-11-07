/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import Colib.KTheory.Waldhausen.Iterated.RowLoopHomotopy

noncomputable section
open CategoryTheory CategoryTheory.Functor MonoidalCategory
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory SSet Topology
open scoped Simplicial Topology unitInterval
universe u v

namespace WaldhausenRowTransformationTests

variable {V W : WideSubcategory preservesZero.{u}} {F G : V ⟶ W}
  (η : F.hom.toFunctor ⟶ G.hom.toFunctor) (hη : ∀ A, W.obj.waldhausen.weq (η.app A))

-- The original transpose square includes both specified endpoint identifications.
example (m n : SimplexCategory) :
    whiskerRight (rowsTransformation (rowsTransformation η n) m)
        (rowSwap W m n).hom.hom.toFunctor ≫
      eqToHom (congrArg (fun f ↦ f.hom.toFunctor) ((rowsInterchange m n).hom.naturality G)) =
    eqToHom (congrArg (fun f ↦ f.hom.toFunctor) ((rowsInterchange m n).hom.naturality F)) ≫
      whiskerLeft (rowSwap V m n).hom.hom.toFunctor
        (rowsTransformation (rowsTransformation η m) n) :=
  rowsTransformation_rowSwap_square η m n

example (k : ℕ) (n : SimplexCategoryᵒᵖ)
    (A : ((stages (k + 2)).obj V).obj n) (τ : (Δ[1]).obj n) :
    (prolongRowSwap (stages k) W).app n
        (stageTransformationFunction (k + 2) η hη n A τ) =
      stageTransformationFunction (k + 2) η hη n
        ((prolongRowSwap (stages k) V).app n A) τ :=
  stageTransformationFunction_rowSwap k η hη n A τ

example (k : ℕ) :
    stageTransformationCylinder (k + 2) η hη ≫ prolongRowSwap (stages k) W =
      (prolongRowSwap (stages k) V ▷ Δ[1]) ≫ stageTransformationCylinder (k + 2) η hη :=
  stageTransformationCylinder_rowSwap k η hη

example (k : ℕ) (t : unitInterval) (x : stageSpace (k + 2) V) :
    stageRowSwapHomeomorph k W (stageTransformationTopHomotopy (k + 2) η hη (t, x)) =
      stageTransformationTopHomotopy (k + 2) η hη (t, stageRowSwapHomeomorph k V x) :=
  stageTransformationTopHomotopy_rowSwap k η hη t x

-- Transformation time and coefficient-loop time remain independent.
example (k : ℕ) (γ : Path (stagePoint (k + 1) V) (stagePoint (k + 1) V))
    (t s : unitInterval) :
    rowLoopStageHomotopy η hη k (t, γ) s =
      stageTransformationTopHomotopy (k + 1) η hη (t, γ s) := rfl

example (k : ℕ) (t : unitInterval) :
    rowLoopStageHomotopy η hη k (t, Path.refl (stagePoint (k + 1) V)) =
      Path.refl (stagePoint (k + 1) W) := rowLoopStageHomotopy_point η hη k t

-- Zero is the genuine additional loop: all three times survive.
example (β : Path (Path.refl (stagePoint 1 V)) (Path.refl (stagePoint 1 V)))
    (t r s : unitInterval) :
    rowLoopZeroHomotopy η hη (t, β) r s =
      stageTransformationTopHomotopy 1 η hη (t, β r s) := rfl

example (t : unitInterval) :
    rowLoopZeroHomotopy η hη (t, Path.refl (Path.refl (stagePoint 1 V))) =
      Path.refl (Path.refl (stagePoint 1 W)) := by
  apply Path.ext
  funext r
  exact rowLoopStageHomotopy_point η hη 0 t

example : (rowLoopTransformationHomotopy η hη).level 0 = rowLoopZeroHomotopy η hη := rfl

example (k : ℕ) :
    (rowLoopTransformationHomotopy η hη).level (k + 1) = rowLoopStageHomotopy η hη k := rfl

-- Both endpoints, the whole fixed-point law, and the coherent structure square.
example (n : ℕ) (x : (rowLoopPrespectrum V).space n) :
    (rowLoopTransformationHomotopy η hη).level n (0, x) = (rowLoopMap F).map n x :=
  (rowLoopTransformationHomotopy η hη).at_zero n x

example (n : ℕ) (x : (rowLoopPrespectrum V).space n) :
    (rowLoopTransformationHomotopy η hη).level n (1, x) = (rowLoopMap G).map n x :=
  (rowLoopTransformationHomotopy η hη).at_one n x

example (n : ℕ) (t : unitInterval) :
    (rowLoopTransformationHomotopy η hη).level n (t, (rowLoopPrespectrum V).point n) =
      (rowLoopPrespectrum W).point n := (rowLoopTransformationHomotopy η hη).at_point n t

example (n : ℕ) (t r : unitInterval) (x : (rowLoopPrespectrum V).space n) :
    (rowLoopTransformationHomotopy η hη).level (n + 1)
        (t, (rowLoopPrespectrum V).structureMap n x r) =
      (rowLoopPrespectrum W).structureMap n
        ((rowLoopTransformationHomotopy η hη).level n (t, x)) r :=
  (rowLoopTransformationHomotopy η hη).comm n t x r

-- The positive square keeps transformation, structure and coefficient times distinct.
example (k : ℕ) (γ : Path (stagePoint (k + 1) V) (stagePoint (k + 1) V))
    (t r s : unitInterval) :
    stageTransformationTopHomotopy (k + 2) η hη
        (t, stageRowSwapHomeomorph k V (stageLoopMap (k + 1) V (γ s) r)) =
      stageRowSwapHomeomorph k W (stageLoopMap (k + 1) W
        (stageTransformationTopHomotopy (k + 1) η hη (t, γ s)) r) := by
  exact congrArg (fun p : Path (stagePoint (k + 2) W) (stagePoint (k + 2) W) ↦ p s)
    ((rowLoopTransformationHomotopy η hη).comm (k + 1) t γ r)

example (β : Path (Path.refl (stagePoint 1 V)) (Path.refl (stagePoint 1 V)))
    (t r : unitInterval) :
    rowLoopStageHomotopy η hη 0 (t, β r) = rowLoopZeroHomotopy η hη (t, β) r :=
  (rowLoopTransformationHomotopy η hη).comm 0 t β r

-- Every time slice is an actual prespectrum morphism, not merely a stable map.
example (t : unitInterval) : rowLoopPrespectrum V ⟶ rowLoopPrespectrum W :=
  (rowLoopTransformationHomotopy η hη).at t

example : (rowLoopTransformationHomotopy η hη).at 0 = rowLoopMap F :=
  LoopPrespectrum.Homotopy.at_zero_eq _

example : (rowLoopTransformationHomotopy η hη).at 1 = rowLoopMap G :=
  LoopPrespectrum.Homotopy.at_one_eq _

-- Endpoint casts preserve each entire continuous level.
example (n : ℕ) :
    (((prespectrumTransformationHomotopy η hη).postcomp (rowStabilizationMap W)).cast
        (rowStabilizationMap_naturality F) (rowStabilizationMap_naturality G)).level n =
      ((prespectrumTransformationHomotopy η hη).postcomp (rowStabilizationMap W)).level n :=
  LoopPrespectrum.Homotopy.cast_level _ _ _ n

example (k : ℕ) (t s : unitInterval) (x : stageSpace k V) :
    Path.toContinuousMap
        (((prespectrumTransformationHomotopy η hη).postcomp
          (rowStabilizationMap W)).level (k + 1) (t, x)) s =
      stageLoopMap k W (stageTransformationTopHomotopy k η hη (t, x)) s := rfl

example (γ : Path (stagePoint 0 V) (stagePoint 0 V)) (t r s : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap
        (((prespectrumTransformationHomotopy η hη).postcomp
          (rowStabilizationMap W)).level 0 (t, γ)) r) s =
      stageLoopMap 0 W (stageTransformationTopHomotopy 0 η hη (t, γ r)) s := rfl

example (k : ℕ) (t s : unitInterval) (x : stageSpace k V) :
    Path.toContinuousMap
        (((rowLoopTransformationHomotopy η hη).precomp
          (rowStabilizationMap V)).level (k + 1) (t, x)) s =
      stageTransformationTopHomotopy (k + 1) η hη (t, stageLoopMap k V x s) := rfl

example (γ : Path (stagePoint 0 V) (stagePoint 0 V)) (t r s : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap
        (((rowLoopTransformationHomotopy η hη).precomp
          (rowStabilizationMap V)).level 0 (t, γ)) r) s =
      stageTransformationTopHomotopy 1 η hη (t, stageLoopMap 0 V (γ r) s) := rfl

-- The exact requested endpoint is equality of whole coherent homotopies.
example :
    ((prespectrumTransformationHomotopy η hη).postcomp (rowStabilizationMap W)).cast
        (rowStabilizationMap_naturality F) (rowStabilizationMap_naturality G) =
      (rowLoopTransformationHomotopy η hη).precomp (rowStabilizationMap V) :=
  rowStabilizationMap_transformation η hη

example (t : unitInterval) :
    (((prespectrumTransformationHomotopy η hη).postcomp (rowStabilizationMap W)).cast
        (rowStabilizationMap_naturality F) (rowStabilizationMap_naturality G)).at t =
      ((rowLoopTransformationHomotopy η hη).precomp (rowStabilizationMap V)).at t :=
  congrArg (fun H ↦ H.at t) (rowStabilizationMap_transformation η hη)

-- Independent original object and hom universes enter through the existing small replacement.
section OriginalUniverses
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (WC : Structure C) (WD : Structure D) {J K : C ⥤ D}
  (hJ : IsExact WC.cof WC.weq WD.cof WD.weq J)
  (hK : IsExact WC.cof WC.weq WD.cof WD.weq K)
  (h0J : J.obj WC.zero = WD.zero) (h0K : K.obj WC.zero = WD.zero)
  (θ : J ⟶ K) (hθ : ∀ A, WD.weq (θ.app A))

example :
    ((originalPrespectrumTransformationHomotopy WC WD hJ hK h0J h0K θ hθ).postcomp
        (rowStabilizationMap (asSmallCategory WD))).cast
      (rowStabilizationMap_naturality (asSmallCategoryMap WC WD hJ h0J))
      (rowStabilizationMap_naturality (asSmallCategoryMap WC WD hK h0K)) =
    (rowLoopTransformationHomotopy
      (F := asSmallCategoryMap WC WD hJ h0J) (G := asSmallCategoryMap WC WD hK h0K)
      (whiskerLeft AsSmall.down (whiskerRight θ AsSmall.up))
      (fun A ↦ hθ (AsSmall.down.obj A))).precomp (rowStabilizationMap (asSmallCategory WC)) :=
  rowStabilizationMap_transformation
    (F := asSmallCategoryMap WC WD hJ h0J) (G := asSmallCategoryMap WC WD hK h0K)
    (whiskerLeft AsSmall.down (whiskerRight θ AsSmall.up)) (fun A ↦ hθ (AsSmall.down.obj A))
end OriginalUniverses

end WaldhausenRowTransformationTests
