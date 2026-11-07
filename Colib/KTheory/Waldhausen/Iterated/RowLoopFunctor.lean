/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Waldhausen.Iterated.RowLoopPrespectrum

/-!
# Exact input functoriality of the distinguished-row prespectrum

Original exact based model maps act on the entire row-loop prespectrum. The genuine row
transpose is natural in those maps, so the distinguished row is preserved without suppressing
its structure permutation. The original row-stabilization maps form a whole natural
transformation. These are model-level input identities, before tensor or support adapters.
-/
/-! Implementation provenance:
`Quillen/Waldhausen/SConstruction/Iterated/RowLoopFunctor.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
row transpose, based maps, independent time coordinates and hypotheses are retained.
The existing native wide category of zero-preserving exact maps supplies the original models. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor
open scoped Topology unitInterval
universe u
namespace CategoryTheory.Waldhausen.IteratedS

open SmallWaldhausenCategory SSet Topology

/-- Naturality of the whole realized transpose, on the original stage maps. -/
theorem stageRowSwapHomeomorph_naturality (k : ℕ) {V W : WideSubcategory preservesZero.{u}}
    (F : V ⟶ W)
    (x : stageSpace (k + 2) V) :
    stageRowSwapHomeomorph k W (SSet.toTop.map ((stages (k + 2)).map F) x) =
      SSet.toTop.map ((stages (k + 2)).map F) (stageRowSwapHomeomorph k V x) := by
  have h := congrArg SSet.toTop.map (prolongRowSwap_naturality (stages k) F)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at h
  exact ConcreteCategory.congr_hom h x

/-- The actual input map on a positive distinguished-row level. -/
def rowLoopStageMap (k : ℕ) {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W) :
    C(Path (stagePoint (k + 1) V) (stagePoint (k + 1) V),
      Path (stagePoint (k + 1) W) (stagePoint (k + 1) W)) :=
  basedLoopMap (SSet.toTop.map ((stages (k + 1)).map F)).hom (stageMap_point (k + 1) F)

/-- Every positive input map preserves the original constant coefficient loop. -/
theorem rowLoopStageMap_point (k : ℕ) {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W) :
    rowLoopStageMap k F (Path.refl (stagePoint (k + 1) V)) =
      Path.refl (stagePoint (k + 1) W) := basedLoopMap_refl _ _

/-- The input square retains both the row parameter and the structure parameter. -/
theorem rowLoopStageStructure_naturality (k : ℕ) {V W : WideSubcategory preservesZero.{u}}
    (F : V ⟶ W)
    (γ : Path (stagePoint (k + 1) V) (stagePoint (k + 1) V)) :
    basedLoopMap (rowLoopStageMap (k + 1) F) (rowLoopStageMap_point (k + 1) F)
      (rowLoopStageStructure k V γ) =
        rowLoopStageStructure k W (rowLoopStageMap k F γ) := by
  apply Path.ext
  funext r
  apply Path.ext
  funext s
  change SSet.toTop.map ((stages (k + 2)).map F)
    (stageRowSwapHomeomorph k V (stageLoopMap (k + 1) V (γ s) r)) =
      stageRowSwapHomeomorph k W
        (stageLoopMap (k + 1) W (SSet.toTop.map ((stages (k + 1)).map F) (γ s)) r)
  rw [← stageRowSwapHomeomorph_naturality]
  exact congrArg (stageRowSwapHomeomorph k W)
    (congrArg (fun p => p r) (stageLoopMap_naturality (k + 1) F (γ s)))

/-- The whole original exact model input map on the distinguished-row prespectrum. -/
def rowLoopMap {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W) :
    rowLoopPrespectrum V ⟶ rowLoopPrespectrum W where
  map n := Nat.casesOn n
    (basedLoopMap (rowLoopStageMap 0 F) (rowLoopStageMap_point 0 F))
    (fun k => rowLoopStageMap k F)
  map_point n := by
    cases n with
    | zero => exact basedLoopMap_refl _ _
    | succ k => exact rowLoopStageMap_point k F
  comm n x := by
    cases n with
    | zero => rfl
    | succ k => exact rowLoopStageStructure_naturality k F x

/-- Distinguished-row loops form an actual functor on the original exact based models. -/
def rowLoopFunctor : WideSubcategory preservesZero.{u} ⥤ LoopPrespectrum.{u} where
  obj := rowLoopPrespectrum
  map := rowLoopMap
  map_id W := by
    apply LoopPrespectrum.Hom.ext
    funext n
    apply ContinuousMap.ext
    intro γ
    cases n with
    | zero =>
      change Path (Path.refl _) (Path.refl _) at γ
      apply Path.ext
      funext r
      apply Path.ext
      funext s
      change SSet.toTop.map ((stages 1).map (𝟙 W)) (γ r s) = γ r s
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
      rfl
    | succ k =>
      change Path _ _ at γ
      apply Path.ext
      funext s
      change SSet.toTop.map ((stages (k + 1)).map (𝟙 W)) (γ s) = γ s
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
      rfl
  map_comp F G := by
    apply LoopPrespectrum.Hom.ext
    funext n
    apply ContinuousMap.ext
    intro γ
    cases n with
    | zero =>
      change Path (Path.refl _) (Path.refl _) at γ
      apply Path.ext
      funext r
      apply Path.ext
      funext s
      change SSet.toTop.map ((stages 1).map (F ≫ G)) (γ r s) =
        SSet.toTop.map ((stages 1).map G) (SSet.toTop.map ((stages 1).map F) (γ r s))
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
      rfl
    | succ k =>
      change Path _ _ at γ
      apply Path.ext
      funext s
      change SSet.toTop.map ((stages (k + 1)).map (F ≫ G)) (γ s) =
        SSet.toTop.map ((stages (k + 1)).map G)
          (SSet.toTop.map ((stages (k + 1)).map F) (γ s))
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
      rfl

/-- The unchanged original row cylinders are natural as whole prespectrum maps. -/
theorem rowStabilizationMap_naturality {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W) :
    prespectrumMap F ≫ rowStabilizationMap W = rowStabilizationMap V ≫ rowLoopMap F := by
  apply LoopPrespectrum.Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  cases n with
  | zero =>
    change Path _ _ at x
    apply Path.ext
    funext r
    exact (stageLoopMap_naturality 0 F (x r)).symm
  | succ k => exact (stageLoopMap_naturality k F x).symm

/-- The canonical row stabilization, with its full exact-model naturality. -/
def rowStabilization : prespectrumFunctor ⟶ rowLoopFunctor where
  app := rowStabilizationMap
  naturality _ _ F := rowStabilizationMap_naturality F

end CategoryTheory.Waldhausen.IteratedS
