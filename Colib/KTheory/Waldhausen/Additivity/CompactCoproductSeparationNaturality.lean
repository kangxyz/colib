/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Additivity.CompactCoproductChangeWeak
public import Colib.KTheory.Waldhausen.Additivity.CompactCoproductSpatial
public import Colib.CategoryTheory.Waldhausen.SConstruction.WeakNaturalTransformationNaturality
public import Colib.Topology.Realization.HomotopySquare

public import Colib.Util.References

/-! # Whole original spatial separation naturality

Both original unit cylinders, both coordinate delays and every point of the compact separation
commute with the actual change-weak map. The path statement retains both endpoint casts, and
the mapped supplied null path retains its target cast to the original constant cube.
-/
/-! Adapted from `Quillen/Waldhausen/Additivity/CompactCoproductSeparationNaturality.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original universes, canonical maps,
coordinates and boundaries are retained. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Topology SSet
open CategoryTheory.Waldhausen.Product
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor MonoidalCategory
open scoped Topology Simplicial unitInterval
universe u v
namespace CategoryTheory.Waldhausen.Additivity
open Fibration

variable {C : Type u} [Category.{v} C] (W : Structure C) (N : NestedWeakEquivalences W)
  [HasBinaryCoproducts C]

/-- The whole original zero-left unit cylinder commutes with weak enlargement. -/
theorem coproductLeftUnitHomotopy_changeWeak (t : unitInterval) (x : W.Delooping) :
    changeWeakMap N (coproductLeftUnitHomotopy W (t, x)) =
      coproductLeftUnitHomotopy N.coarse (t, changeWeakMap N x) := by
  have hs : sSetMap (changeWeak_exact N) ▷ Δ[1] ≫
      weakNaturalTransformationCylinder N.coarse N.coarse
        ((secondEmbedding_isExact N.coarse).comp (coproductRebasedFunctor_exact N.coarse))
        (IsExact.id N.coarse.cof N.coarse.weq) (coproductLeftUnitIso N.coarse).hom
        (fun _ ↦ N.coarse.weq_iso _ inferInstance) =
      weakNaturalTransformationCylinder W W
        ((secondEmbedding_isExact W).comp (coproductRebasedFunctor_exact W))
        (IsExact.id W.cof W.weq) (coproductLeftUnitIso W).hom
        (fun _ ↦ W.weq_iso _ inferInstance) ≫ sSetMap (changeWeak_exact N) := by
    rw [weakNaturalTransformationCylinder_precompose,
      weakNaturalTransformationCylinder_postcompose]
    cases W
    rcases N with ⟨coarse, hcof, hzero, hw⟩
    cases coarse
    cases hzero
    rfl
  exact SSet.realizationSimplicialHomotopy_square _ _ (sSetMap (changeWeak_exact N))
    (sSetMap (changeWeak_exact N)) hs.symm t x

/-- The whole original zero-right unit cylinder commutes with the same map. -/
theorem coproductRightUnitHomotopy_changeWeak (t : unitInterval) (x : W.Delooping) :
    changeWeakMap N (coproductRightUnitHomotopy W (t, x)) =
      coproductRightUnitHomotopy N.coarse (t, changeWeakMap N x) := by
  have hs : sSetMap (changeWeak_exact N) ▷ Δ[1] ≫
      weakNaturalTransformationCylinder N.coarse N.coarse
        ((firstEmbedding_isExact N.coarse).comp (coproductRebasedFunctor_exact N.coarse))
        (IsExact.id N.coarse.cof N.coarse.weq) (coproductRightUnitIso N.coarse).hom
        (fun _ ↦ N.coarse.weq_iso _ inferInstance) =
      weakNaturalTransformationCylinder W W
        ((firstEmbedding_isExact W).comp (coproductRebasedFunctor_exact W))
        (IsExact.id W.cof W.weq) (coproductRightUnitIso W).hom
        (fun _ ↦ W.weq_iso _ inferInstance) ≫ sSetMap (changeWeak_exact N) := by
    rw [weakNaturalTransformationCylinder_precompose,
      weakNaturalTransformationCylinder_postcompose]
    cases W
    rcases N with ⟨coarse, hcof, hzero, hw⟩
    cases coarse
    cases hzero
    rfl
  exact SSet.realizationSimplicialHomotopy_square _ _ (sSetMap (changeWeak_exact N))
    (sSetMap (changeWeak_exact N)) hs.symm t x

variable (n : ℕ)

/-- The actual zero-left unit commutes at all original cube coordinates. -/
theorem coproductLeftUnitCubeMap_changeWeak
    (p : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) (t : unitInterval) :
    coproductChangeWeakCubeMap W N n (coproductLeftUnitCubeMap W n (t, p)) =
      coproductLeftUnitCubeMap N.coarse n (t, coproductChangeWeakCubeMap W N n p) := by
  ext z
  exact coproductLeftUnitHomotopy_changeWeak W N t (p z)

/-- The actual zero-right unit commutes at all original cube coordinates. -/
theorem coproductRightUnitCubeMap_changeWeak
    (p : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) (t : unitInterval) :
    coproductChangeWeakCubeMap W N n (coproductRightUnitCubeMap W n (t, p)) =
      coproductRightUnitCubeMap N.coarse n (t, coproductChangeWeakCubeMap W N n p) := by
  ext z
  exact coproductRightUnitHomotopy_changeWeak W N t (p z)

omit [HasBinaryCoproducts C] in
/-- The entire original prefix delay commutes with the unchanged based map. -/
theorem genLoopDelayLeft_changeWeak
    (p : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) (t : unitInterval) :
    coproductChangeWeakCubeMap W N n (genLoopDelayLeft n (t, p)) =
      genLoopDelayLeft n (t, coproductChangeWeakCubeMap W N n p) := by
  ext z
  rfl

omit [HasBinaryCoproducts C] in
/-- The entire original suffix delay commutes with the unchanged based map. -/
theorem genLoopDelayRight_changeWeak
    (p : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) (t : unitInterval) :
    coproductChangeWeakCubeMap W N n (genLoopDelayRight n (t, p)) =
      genLoopDelayRight n (t, coproductChangeWeakCubeMap W N n p) := by
  ext z
  rfl

omit [HasBinaryCoproducts C] in
/-- The old spatial concatenation keeps its exact order after the original map. -/
theorem coproductChangeWeakCubeMap_transAt
    (p q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) :
    coproductChangeWeakCubeMap W N n (GenLoop.transAt 0 p q) =
      GenLoop.transAt 0 (coproductChangeWeakCubeMap W N n p)
        (coproductChangeWeakCubeMap W N n q) :=
  GenLoop.postcomp_transAt (changeWeakMap N) (changeWeakMap_basepoint N) 0 p q

/-- Every original separation time commutes, before passing to paths or homotopy classes. -/
theorem coproductSeparationPath_changeWeak_apply
    (p q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) (t : unitInterval) :
    coproductChangeWeakCubeMap W N n (coproductSeparationPath n W p q t) =
      coproductSeparationPath n N.coarse (coproductChangeWeakCubeMap W N n p)
        (coproductChangeWeakCubeMap W N n q) t := by
  rw [coproductSeparationPath_eq, coproductSeparationPath_eq,
    Path.trans_apply, Path.trans_apply]
  split_ifs
  · change coproductChangeWeakCubeMap W N n
      (coproductCube W n (genLoopDelayLeft n (σ _, p)) (genLoopDelayRight n (σ _, q))) = _
    rw [coproductCube_changeWeak, genLoopDelayLeft_changeWeak, genLoopDelayRight_changeWeak]
    rfl
  · change coproductChangeWeakCubeMap W N n
      (GenLoop.transAt 0 (coproductLeftUnitCubeMap W n (_, q))
        (coproductRightUnitCubeMap W n (_, p))) = _
    rw [coproductChangeWeakCubeMap_transAt, coproductLeftUnitCubeMap_changeWeak,
      coproductRightUnitCubeMap_changeWeak]
    rfl

/-- Both source and target casts of the actual mapped separation path are explicit. -/
theorem coproductSeparationPath_changeWeak
    (p q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) :
    ((coproductSeparationPath n W p q).map (coproductChangeWeakCubeMap W N n).continuous).cast
      (coproductCube_changeWeak W N n p q).symm
      (coproductChangeWeakCubeMap_transAt W N n q p).symm =
        coproductSeparationPath n N.coarse (coproductChangeWeakCubeMap W N n p)
          (coproductChangeWeakCubeMap W N n q) := by
  apply Path.ext
  funext t
  exact coproductSeparationPath_changeWeak_apply W N n p q t

omit [HasBinaryCoproducts C] in
/-- The same original constant cube is retained by the actual change-weak map. -/
theorem coproductChangeWeakCubeMap_const :
    coproductChangeWeakCubeMap W N n GenLoop.const = GenLoop.const :=
  GenLoop.postcomp_const (changeWeakMap N) (changeWeakMap_basepoint N)

omit [HasBinaryCoproducts C] in
/-- The original supplied null path is mapped with its actual constant-target transport. -/
def coproductChangeWeakNullPath
    {c : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint} (P : Path c GenLoop.const) :
    Path (coproductChangeWeakCubeMap W N n c) GenLoop.const :=
  (P.map (coproductChangeWeakCubeMap W N n).continuous).cast rfl
    (coproductChangeWeakCubeMap_const W N n).symm


attribute [colib_tag "COL-0302",
  colib_ref "quillen"
    "Quillen/Waldhausen/Additivity/CompactCoproductSeparationNaturality.lean:163-172" "adaptation"
    "Original compact-coproduct construction with every supplied parameter, boundary \
      and endpoint transport retained"]
  coproductSeparationPath_changeWeak

attribute [colib_tag "COL-0302",
  colib_ref "quillen"
    "Quillen/Waldhausen/Additivity/CompactCoproductSeparationNaturality.lean:182-186" "adaptation"
    "Original compact-coproduct construction with every supplied parameter, boundary \
      and endpoint transport retained"]
  coproductChangeWeakNullPath

end CategoryTheory.Waldhausen.Additivity
