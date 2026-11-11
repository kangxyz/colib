/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.Loop.NormalizationPrism

/-!
# Whole naturality of the parameterized normalization prism

Every time change in the prism is independent of the ambient space and residual input.
Consequently pointwise agreement of the component, self-track, and specified null gives
agreement of the entire three-time prism. Based postcomposition and input reindexing are
special cases. No compatibility with a coordinate-interchanging spectrum structure is asserted.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u v w u' v'
namespace Topology.LoopNormalizationPrism

section Pointwise
variable
    {X : Type u} {Y : Type v} {X' : Type u'} {Y' : Type v'} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    {y : Y} {y' : Y'} (a : Y → Z) (b : Y' → Z)
    (γ : C(X, Path y y)) (α : γ.Homotopy γ)
    (N : γ.Homotopy (ContinuousMap.const X (Path.refl y)))
    (γ' : C(X', Path y' y')) (α' : γ'.Homotopy γ')
    (N' : γ'.Homotopy (ContinuousMap.const X' (Path.refl y')))
    (x : X) (x' : X')

/-- Pointwise dependence of the initial pause removal. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrismNaturality.lean:38"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
theorem leftRemoval_pointwise
    (hγ : ∀ s, a (γ x s) = b (γ' x' s))
    (hα : ∀ t s, a (α (t, x) s) = b (α' (t, x') s))
    (r t s : unitInterval) :
    a (leftRemoval γ α N (r, x) t s) =
      b (leftRemoval γ' α' N' (r, x') t s) := by
  have hpref (t s : unitInterval) :
      a (prefixTrack γ α (t, x) s) = b (prefixTrack γ' α' (t, x') s) := by
    change a (((γ x).symm.trans (α (t, x))) s) =
      b (((γ' x').symm.trans (α' (t, x'))) s)
    simp only [Path.trans_apply, Path.symm_apply]
    split_ifs <;> first | exact hγ _ | exact hα _ _
  change a (leftRemovalFamily γ α (r, x) t s) =
    b (leftRemovalFamily γ' α' (r, x') t s)
  rw [leftRemovalFamily_apply, leftRemovalFamily_apply]
  simp only [Path.trans_apply, Path.symm_apply]
  split_ifs <;> first | exact hγ _ | exact hpref _ _

/-- Pointwise dependence of the full moving-prefix core. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrismNaturality.lean:57"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
theorem coreHomotopy_pointwise
    (hα : ∀ t s, a (α (t, x) s) = b (α' (t, x') s))
    (hN : ∀ t s, a (N (t, x) s) = b (N' (t, x') s))
    (r t s : unitInterval) :
    a (coreHomotopy γ α N (r, x) t s) =
      b (coreHomotopy γ' α' N' (r, x') t s) := by
  have hseg (r t s : unitInterval) :
      a (segment γ N (t, (r, x)) s) = b (segment γ' N' (t, (r, x')) s) := by
    change a (((N (r, x)).symm.trans (N (r * t, x))) s) =
      b (((N' (r, x')).symm.trans (N' (r * t, x'))) s)
    simp only [Path.trans_apply, Path.symm_apply]
    split_ifs <;> exact hN _ _
  have hret (r t s : unitInterval) :
      a (returnPath γ N (t, (r, x)) s) = b (returnPath γ' N' (t, (r, x')) s) := by
    simp only [returnPath, ContinuousMap.Homotopy.trans_apply]
    split_ifs <;> first | exact hseg _ _ _ | exact hN _ _
  have hpre (r t s : unitInterval) :
      a (prefixed γ α N (t, (r, x)) s) = b (prefixed γ' α' N' (t, (r, x')) s) := by
    change a (((N (r, x)).symm.trans (α (t, x))) s) =
      b (((N' (r, x')).symm.trans (α' (t, x'))) s)
    simp only [Path.trans_apply, Path.symm_apply]
    split_ifs <;> first | exact hN _ _ | exact hα _ _
  change a ((movingWord γ α N) (t, (r, x)) s) =
    b ((movingWord γ' α' N') (t, (r, x')) s)
  simp only [movingWord, ContinuousMap.Homotopy.trans_apply,
    ContinuousMap.Homotopy.symm_apply]
  split_ifs <;> first | exact hret _ _ _ | exact hpre _ _ _

/-- Pointwise dependence of the terminal pause removal. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrismNaturality.lean:86"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
theorem rightRemoval_pointwise
    (hy : a y = b y')
    (hα : ∀ t s, a (α (t, x) s) = b (α' (t, x') s))
    (hN : ∀ t s, a (N (t, x) s) = b (N' (t, x') s))
    (r t s : unitInterval) :
    a (rightRemoval γ α N (r, x) t s) =
      b (rightRemoval γ' α' N' (r, x') t s) := by
  have hln (t s : unitInterval) :
      a (leftNull γ N (t, x) s) = b (leftNull γ' N' (t, x') s) := by
    change a (((Path.refl y).trans (N (t, x))) s) =
      b (((Path.refl y').trans (N' (t, x'))) s)
    simp only [Path.trans_apply, Path.refl_apply]
    split_ifs <;> first | exact hy | exact hN _ _
  have hlt (t s : unitInterval) :
      a (leftTrack γ α (t, x) s) = b (leftTrack γ' α' (t, x') s) := by
    change a (((Path.refl y).trans (α (t, x))) s) =
      b (((Path.refl y').trans (α' (t, x'))) s)
    simp only [Path.trans_apply, Path.refl_apply]
    split_ifs <;> first | exact hy | exact hα _ _
  change a (rightRemovalFamily γ α N (r, x) t s) =
    b (rightRemovalFamily γ' α' N' (r, x') t s)
  rw [rightRemovalFamily_apply, rightRemovalFamily_apply]
  simp only [Path.trans_apply, Path.symm_apply]
  split_ifs <;> first | exact hln _ _ | exact hlt _ _

/-- Pointwise dependence of the constant inner-prefix removal. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrismNaturality.lean:112"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
theorem innerRemoval_pointwise
    (hα : ∀ t s, a (α (t, x) s) = b (α' (t, x') s))
    (hN : ∀ t s, a (N (t, x) s) = b (N' (t, x') s))
    (r t s : unitInterval) :
    a (innerRemoval γ α N (r, x) t s) =
      b (innerRemoval γ' α' N' (r, x') t s) := by
  have hn (t s : unitInterval) :
      a (nullConjugate γ α N x t s) = b (nullConjugate γ' α' N' x' t s) := by
    change a ((N.symm.trans (α.trans N)) (t, x) s) =
      b ((N'.symm.trans (α'.trans N')) (t, x') s)
    simp only [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.symm_apply]
    split_ifs <;> first | exact hN _ _ | exact hα _ _
  exact hn _ _

/-- The entire prism depends pointwise on the given component, self-track, and null. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrismNaturality.lean:127"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
theorem normalizationHomotopy_pointwise
    (hγ : ∀ s, a (γ x s) = b (γ' x' s))
    (hα : ∀ t s, a (α (t, x) s) = b (α' (t, x') s))
    (hN : ∀ t s, a (N (t, x) s) = b (N' (t, x') s))
    (r t s : unitInterval) :
    a (normalizationHomotopy γ α N (r, x) t s) =
      b (normalizationHomotopy γ' α' N' (r, x') t s) := by
  have hy : a y = b y' := by simpa using hγ 0
  simp only [normalizationHomotopy, ContinuousMap.Homotopy.trans_apply,
    ContinuousMap.Homotopy.symm_apply]
  split_ifs
  · exact leftRemoval_pointwise a b γ α N γ' α' N' x x' hγ hα _ _ _
  · exact coreHomotopy_pointwise a b γ α N γ' α' N' x x' hα hN _ _ _
  · exact rightRemoval_pointwise a b γ α N γ' α' N' x x' hy hα hN _ _ _
  · exact innerRemoval_pointwise a b γ α N γ' α' N' x x' hα hN _ _ _

end Pointwise

/-- A based map and any input reindexing preserve the whole prism whenever they preserve its data.
The three independent times are unchanged, including the original inner normalization time. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrismNaturality.lean:147"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
theorem normalizationHomotopy_naturality
    {X : Type u} {Y : Type v} {X' : Type u'} {Y' : Type v'}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    {y : Y} {y' : Y'} (f : C(Y, Y')) (hf : f y = y') (k : X' → X)
    (γ : C(X, Path y y)) (α : γ.Homotopy γ)
    (N : γ.Homotopy (ContinuousMap.const X (Path.refl y)))
    (γ' : C(X', Path y' y')) (α' : γ'.Homotopy γ')
    (N' : γ'.Homotopy (ContinuousMap.const X' (Path.refl y')))
    (hγ : ∀ x, basedLoopMap f hf (γ (k x)) = γ' x)
    (hα : ∀ t x, basedLoopMap f hf (α (t, k x)) = α' (t, x))
    (hN : ∀ t x, basedLoopMap f hf (N (t, k x)) = N' (t, x))
    (r : unitInterval) (x : X') :
    basedLoopMap (basedLoopMap f hf) (basedLoopMap_refl f hf)
        (normalizationHomotopy γ α N (r, k x)) =
      normalizationHomotopy γ' α' N' (r, x) := by
  apply Path.ext
  funext t
  apply Path.ext
  funext s
  exact normalizationHomotopy_pointwise f id γ α N γ' α' N' (k x) x
    (fun z ↦ congrArg (fun p : Path y' y' ↦ p z) (hγ x))
    (fun u z ↦ congrArg (fun p : Path y' y' ↦ p z) (hα u x))
    (fun u z ↦ congrArg (fun p : Path y' y' ↦ p z) (hN u x)) r t s

end Topology.LoopNormalizationPrism

attribute [colib_tag "COL-0552"]
  Topology.LoopNormalizationPrism.normalizationHomotopy_naturality
