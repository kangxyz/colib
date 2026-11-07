/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import Colib.KTheory.Waldhausen.Iterated.RowLoopStableEquivalence
import Colib.KTheory.Waldhausen.Iterated.RowLoopFunctor

noncomputable section
open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory SSet Topology
open scoped Simplicial Topology unitInterval
universe u v

namespace WaldhausenRowStabilizationTests

variable (W : WideSubcategory preservesZero.{u}) (k : ℕ)

-- The target keeps the actual zero-stage double-loop extension.
example : (rowLoopPrespectrum W).space 0 =
    TopCat.of (Path (Path.refl (stagePoint 1 W)) (Path.refl (stagePoint 1 W))) := rfl

example : (rowLoopPrespectrum W).space (k + 1) =
    TopCat.of (Path (stagePoint (k + 1) W) (stagePoint (k + 1) W)) := rfl

example : (rowLoopPrespectrum W).structureMap 0 = ContinuousMap.id _ := rfl

example : (rowLoopPrespectrum W).structureMap (k + 1) = rowLoopStageStructure k W := rfl

example : (rowStabilizationMap W).map 0 =
    basedLoopMap (stageLoopMap 0 W) (stageLoopMap_point 0 W) := rfl

example : (rowStabilizationMap W).map (k + 1) = stageLoopMap k W :=
  rowStabilizationMap_succ W k

-- Independent input-loop and new-row parameters must not be silently identified.
example (γ : Path (stagePoint 0 W) (stagePoint 0 W)) (r s : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap ((rowStabilizationMap W).map 0 γ) r) s =
      stageLoopMap 0 W (γ r) s := rowStabilizationMap_zero W γ r s

example (γ : Path (stagePoint (k + 1) W) (stagePoint (k + 1) W))
    (r s : unitInterval) :
    rowLoopStageStructure k W γ r s =
      stageRowSwapHomeomorph k W (stageLoopMap (k + 1) W (γ s) r) :=
  rowLoopStageStructure_apply k W γ r s

example (γ : Path (stagePoint (k + 1) W) (stagePoint (k + 1) W)) (r : unitInterval) :
    rowLoopStageStructure k W γ r =
      basedLoopMap (rowLoopStructureEvaluation k W r)
        (rowLoopStructureEvaluation_point k W r) γ :=
  rowLoopStageStructure_row k W γ r

example (x : stageSpace k W) (s t : unitInterval) :
    stageRowSwapHomeomorph k W (stageLoopMap (k + 1) W (stageLoopMap k W x s) t) =
      stageLoopMap (k + 1) W (stageLoopMap k W x t) s := stageLoopMap_rowSwap k W x s t

-- The interchange is the image of the literal quotient-row transpose.
example (H : WideSubcategory preservesZero.{u} ⥤ SSet.{u}) (n : SimplexCategoryᵒᵖ) :
    (prolongRowSwap H W).app n = (H.map (rowSwap W n.unop n.unop).hom).app n := rfl

example (H : WideSubcategory preservesZero.{u} ⥤ SSet.{u}) :
    (prolongRowSwapIso H W).inv = prolongRowSwap H W := rfl

example (H : WideSubcategory preservesZero.{u} ⥤ SSet.{u}) :
    prolongRowSwap H W ≫ prolongRowSwap H W = 𝟙 _ := prolongRowSwap_comp_self H W

example {m n : SimplexCategory} (θ : m ⟶ ⦋1⦌) (τ : n ⟶ ⦋1⦌) :
    ((insertion θ).app W ≫ (rows m).map ((insertion τ).app W)) ≫
      (rowSwap W m n).hom =
        (insertion τ).app W ≫ (rows n).map ((insertion θ).app W) :=
  insertion_insertion_rowSwap W θ τ

example {m n : SimplexCategory} (α : m ⟶ n) :
    (rowSwap W n n).hom ≫ diagonalRowsReindex W α =
      diagonalRowsReindex W α ≫ (rowSwap W m m).hom := rowSwap_diagonalReindex W α

-- Check strict whole-spectrum compatibility, not just weak levels.
example (n : ℕ) (x : (prespectrum W).space n) :
    basedLoopMap ((rowStabilizationMap W).map (n + 1))
      ((rowStabilizationMap W).map_point (n + 1)) ((prespectrum W).structureMap n x) =
      (rowLoopPrespectrum W).structureMap n ((rowStabilizationMap W).map n x) :=
  (rowStabilizationMap W).comm n x

example : IsWeakHomotopyEquivalence ((rowStabilizationMap W).map 0) :=
  rowStabilizationMap_weak W 0

example (n : ℕ) : IsWeakHomotopyEquivalence ((rowStabilizationMap W).map n) :=
  rowStabilizationMap_weak W n

example (n : ℕ) (x : (prespectrum W).space n) (q : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin q)
      ((rowStabilizationMap W).map n) (x := x) rfl) :=
  (rowStabilizationMap_weak W n).homotopy_bijective x q

example : LoopPrespectrum.IsStableEquivalence (rowStabilizationMap W) :=
  rowStabilizationMap_isStableEquivalence W

-- This is the actual induced map, in an arbitrary integer degree.
example (d : ℤ) : IsIso ((LoopPrespectrum.stableHomotopyFunctor d).map
    (rowStabilizationMap W)) := rowStabilizationMap_isStableEquivalence W d

example : IsIso ((LoopPrespectrum.stableHomotopyFunctor (-7)).map
    (rowStabilizationMap W)) := rowStabilizationMap_isStableEquivalence W (-7)

example : IsIso ((LoopPrespectrum.stableHomotopyFunctor 0).map
    (rowStabilizationMap W)) := rowStabilizationMap_isStableEquivalence W 0

example : IsIso ((LoopPrespectrum.stableHomotopyFunctor 5).map
    (rowStabilizationMap W)) := rowStabilizationMap_isStableEquivalence W 5

variable {V : WideSubcategory preservesZero.{u}} (F : V ⟶ W)

example : prespectrumMap F ≫ rowStabilizationMap W =
    rowStabilizationMap V ≫ rowLoopMap F := rowStabilizationMap_naturality F

example : rowStabilization.app W = rowStabilizationMap W := rfl

example : rowLoopFunctor.map F = rowLoopMap F := rfl

example : (rowLoopMap F).map 0 =
    basedLoopMap (rowLoopStageMap 0 F) (rowLoopStageMap_point 0 F) := rfl

example (γ : Path (stagePoint (k + 1) V) (stagePoint (k + 1) V)) :
    basedLoopMap (rowLoopStageMap (k + 1) F) (rowLoopStageMap_point (k + 1) F)
      (rowLoopStageStructure k V γ) =
        rowLoopStageStructure k W (rowLoopStageMap k F γ) :=
  rowLoopStageStructure_naturality k F γ

-- Arbitrary independent object/morphism universes use the existing native model unchanged.
section OriginalUniverses
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (WC : Structure C) (WD : Structure D) {G : C ⥤ D}
  (hG : IsExact WC.cof WC.weq WD.cof WD.weq G) (h0 : G.obj WC.zero = WD.zero)

example : originalPrespectrum WC ⟶ rowLoopPrespectrum (asSmallCategory WC) :=
  rowStabilizationMap (asSmallCategory WC)

example (d : ℤ) : IsIso ((LoopPrespectrum.stableHomotopyFunctor d).map
    (rowStabilizationMap (asSmallCategory WC))) :=
  rowStabilizationMap_isStableEquivalence (asSmallCategory WC) d

example : originalPrespectrumMap WC WD hG h0 ≫ rowStabilizationMap (asSmallCategory WD) =
    rowStabilizationMap (asSmallCategory WC) ≫ rowLoopMap (asSmallCategoryMap WC WD hG h0) :=
  rowStabilizationMap_naturality (asSmallCategoryMap WC WD hG h0)
end OriginalUniverses

end WaldhausenRowStabilizationTests
