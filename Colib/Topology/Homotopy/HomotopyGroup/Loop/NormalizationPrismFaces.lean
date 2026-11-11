/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.Loop.NormalizationPrismCore

/-!
# The exact end words of the moving-prefix prism

These formulas retain the specified inverse-prefix cancellation and the supplied null.
The two extra pauses are displayed explicitly; they will be removed by continuous path
reparametrizations. The result concerns actual paths, not their homotopy classes.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u v
namespace Topology.LoopNormalizationPrism
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {y : Y}


/-- Pointwise comparison of complete null-conjugation words, with distinct base presentations. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrismFaces.lean:38"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
theorem conjugation_pointwise {f : C(X, Y)} {b : Y}
    (H : f.Homotopy f) (N : f.Homotopy (ContinuousMap.const X b))
    {a : Y} (p : Path a a) (q : Path a b) (x : X)
    (hp : ∀ t, H (t, x) = p t) (hq : ∀ t, N (t, x) = q t) (t : unitInterval) :
    (N.symm.trans (H.trans N)) (t, x) = (q.symm.trans (p.trans q)) t := by
  simp only [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.symm_apply,
    Path.trans_apply, Path.symm_apply]
  split_ifs <;> first | exact hp _ | exact hq _

variable (γ : C(X, Path y y)) (α : γ.Homotopy γ)
  (N : γ.Homotopy (ContinuousMap.const X (Path.refl y)))




/-- The moving return has precisely one initial constant pause at its zero face. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrismFaces.lean:103"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
theorem returnPath_zero (t : unitInterval) (x : X) :
    returnPath γ N (t, (0, x)) =
      ((Path.refl ((γ x).symm.trans (γ x))).trans (loopInversePrefixCancellation (γ x))) t := by
  simp only [returnPath, ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
  split_ifs
  · change (N (0, x)).symm.trans (N (0 * _, x)) = _
    simp
  · change loopInversePrefixCancellation (N (0, x)) _ = _
    rw [N.apply_zero]

/-- The moving prefix retains the original complete self-track at its zero face. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrismFaces.lean:114"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
theorem prefixed_zero (t : unitInterval) (x : X) :
    prefixed γ α N (t, (0, x)) = prefixTrack γ α (t, x) := by
  change (N (0, x)).symm.trans (α (t, x)) = (γ x).symm.trans (α (t, x))
  rw [N.apply_zero]

/-- The whole zero face, including both paused occurrences of the original cancellation. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrismFaces.lean:120"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
theorem family_zero_face (x : X) :
    family γ α N (0, x) =
      ((Path.refl ((γ x).symm.trans (γ x))).trans
        (loopInversePrefixCancellation (γ x))).symm.trans
          (((prefixTrack γ α).evalAt x).trans
            ((Path.refl ((γ x).symm.trans (γ x))).trans
              (loopInversePrefixCancellation (γ x)))) := by
  apply Path.ext
  funext t
  exact conjugation_pointwise (prefixed γ α N) (returnPath γ N) _ _ (0, x)
    (fun s ↦ prefixed_zero γ α N s x) (fun s ↦ returnPath_zero γ N s x) t

/-- The constant inverse-prefix cancellation remains the constant inner loop at every time. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrismFaces.lean:133"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
theorem cancellation_refl (t : unitInterval) :
    loopInversePrefixCancellation (Path.refl y) t = Path.refl y := by
  ext s
  rfl

/-- The null with a fixed constant prefix on every inner loop. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrismFaces.lean:139"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
def leftNull : ((⟨fun x ↦ (Path.refl y).trans (γ x),
    Path.continuous_trans.comp (continuous_const.prodMk γ.continuous)⟩ : C(X, Path y y))).Homotopy
      (ContinuousMap.const X (Path.refl y)) where
  toFun z := (Path.refl y).trans (N z)
  continuous_toFun := Path.continuous_trans.comp (continuous_const.prodMk N.continuous)
  map_zero_left x := by simp
  map_one_left x := by simp

/-- The self-track with the same fixed constant inner prefix. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrismFaces.lean:148"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
def leftTrack : ((⟨fun x ↦ (Path.refl y).trans (γ x),
    Path.continuous_trans.comp (continuous_const.prodMk γ.continuous)⟩ : C(X, Path y y))).Homotopy
      ⟨fun x ↦ (Path.refl y).trans (γ x),
        Path.continuous_trans.comp (continuous_const.prodMk γ.continuous)⟩ where
  toFun z := (Path.refl y).trans (α z)
  continuous_toFun := Path.continuous_trans.comp (continuous_const.prodMk α.continuous)
  map_zero_left x := by simp
  map_one_left x := by simp

/-- The moving return has exactly one terminal constant pause at its one face. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrismFaces.lean:158"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
theorem returnPath_one (t : unitInterval) (x : X) :
    returnPath γ N (t, (1, x)) =
      (((leftNull γ N).evalAt x).trans (Path.refl (Path.refl y))) t := by
  simp only [returnPath, ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
  split_ifs
  · change (N (1, x)).symm.trans (N (1 * _, x)) = (Path.refl y).trans (N (_, x))
    simp
  · change loopInversePrefixCancellation (N (1, x)) _ = Path.refl y
    rw [N.apply_one]
    exact cancellation_refl _

/-- The moving self-track has a constant inner prefix at its one face. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrismFaces.lean:170"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
theorem prefixed_one (t : unitInterval) (x : X) :
    prefixed γ α N (t, (1, x)) = leftTrack γ α (t, x) := by
  change (N (1, x)).symm.trans (α (t, x)) = (Path.refl y).trans (α (t, x))
  simp

/-- The whole one face, with its terminal pauses and its constant inner prefix still visible. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrismFaces.lean:176"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
theorem family_one_face (x : X) :
    family γ α N (1, x) =
      (((leftNull γ N).evalAt x).trans (Path.refl (Path.refl y))).symm.trans
        (((leftTrack γ α).evalAt x).trans
          (((leftNull γ N).evalAt x).trans (Path.refl (Path.refl y)))) := by
  apply Path.ext
  funext t
  exact conjugation_pointwise (prefixed γ α N) (returnPath γ N) _ _ (1, x)
    (fun s ↦ prefixed_one γ α N s x) (fun s ↦ returnPath_one γ N s x) t

end Topology.LoopNormalizationPrism
