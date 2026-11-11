/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.Loop.NormalizedSelfTrackFamily

/-!
# The continuous moving-prefix core for original loop normalization

A continuous family of self-tracks at varying loop components, together with a supplied
continuous null of those components, gives an explicit family of based loops. The prefix
slides along that same null; its return uses the initial segment of the null followed by
the original inverse-prefix cancellation. Every residual input parameter remains independent.

This is a topology-level comparison for the existing specified normalization. It asserts no
prespectrum structure compatibility: the untransposed inner-loop structure requires its own
row-interchange certificate in the tensor first-coefficient application.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u v
namespace Topology.LoopNormalizationPrism
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {y : Y}

/-- Original inverse-prefix cancellation is jointly continuous in its path and time. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrismCore.lean:32"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
theorem cancellation_continuous :
    Continuous (fun z : unitInterval × Path y y ↦ loopInversePrefixCancellation z.2 z.1) := by
  apply Path.continuous_uncurry_iff.mp
  change Continuous (fun z : (unitInterval × Path y y) × unitInterval ↦
    z.1.2 (unitInterval.symm ⟨Path.Homotopy.reflTransSymmAux
      (unitInterval.symm z.1.1, z.2), Path.Homotopy.reflTransSymmAux_mem_I _⟩))
  fun_prop


variable (γ : C(X, Path y y)) (α : γ.Homotopy γ)
  (N : γ.Homotopy (ContinuousMap.const X (Path.refl y)))

/-- The moving inverse prefix applied to the unchanged initial component. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrismCore.lean:52"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
def base : C(unitInterval × X, Path y y) :=
  ⟨fun z ↦ (N z).symm.trans (γ z.2),
    Path.continuous_trans.comp
      ((Path.continuous_symm.comp N.continuous).prodMk
        (γ.continuous.comp continuous_snd))⟩

/-- The moving inverse prefix applied to its own current component. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrismCore.lean:59"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
def diagonal : C(unitInterval × X, Path y y) :=
  ⟨fun z ↦ (N z).symm.trans (N z),
    Path.continuous_trans.comp
      ((Path.continuous_symm.comp N.continuous).prodMk N.continuous)⟩

/-- The complete self-track under the displayed moving inverse prefix. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrismCore.lean:65"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
def prefixed : (base γ N).Homotopy (base γ N) where
  toFun z := (N z.2).symm.trans (α (z.1, z.2.2))
  continuous_toFun := Path.continuous_trans.comp
    ((Path.continuous_symm.comp (N.continuous.comp continuous_snd)).prodMk
      (α.continuous.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))))
  map_zero_left x := by simp [base]
  map_one_left x := by simp [base]

/-- The actual initial segment of N, multiplied by the fixed current inverse prefix. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrismCore.lean:74"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
def segment : (base γ N).Homotopy (diagonal γ N) where
  toFun z := (N z.2).symm.trans (N (z.2.1 * z.1, z.2.2))
  continuous_toFun := Path.continuous_trans.comp
    ((Path.continuous_symm.comp (N.continuous.comp continuous_snd)).prodMk
      (N.continuous.comp (by fun_prop)))
  map_zero_left x := by simp [base]
  map_one_left x := by simp [diagonal]

/-- The same original cancellation at each current component of N. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrismCore.lean:83"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
def cancellation : (diagonal γ N).Homotopy
    (ContinuousMap.const (unitInterval × X) (Path.refl y)) where
  toFun z := loopInversePrefixCancellation (N z.2) z.1
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z : (unitInterval × (unitInterval × X)) × unitInterval ↦
      N z.1.2 (unitInterval.symm ⟨Path.Homotopy.reflTransSymmAux
        (unitInterval.symm z.1.1, z.2), Path.Homotopy.reflTransSymmAux_mem_I _⟩))
    fun_prop
  map_zero_left x := (loopInversePrefixCancellation (N x)).source
  map_one_left x := (loopInversePrefixCancellation (N x)).target

/-- Return from the moving base by the supplied null segment and the original cancellation. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrismCore.lean:96"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
def returnPath : (base γ N).Homotopy
    (ContinuousMap.const (unitInterval × X) (Path.refl y)) :=
  (segment γ N).trans (cancellation γ N)

/-- The original null-conjugation word, with both independent prism and self-track times. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrismCore.lean:101"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
def movingWord : (ContinuousMap.const (unitInterval × X) (Path.refl y)).Homotopy
    (ContinuousMap.const (unitInterval × X) (Path.refl y)) :=
  (returnPath γ N).symm.trans ((prefixed γ α N).trans (returnPath γ N))

/-- The jointly continuous based loop family underlying the moving-prefix prism. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrismCore.lean:106"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
def family : C(unitInterval × X, Path (Path.refl y) (Path.refl y)) :=
  basedFamily (movingWord γ α N)

/-- Both original outer-loop endpoints remain at the constant inner loop. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrismCore.lean:110"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
theorem family_zero (r : unitInterval) (x : X) : family γ α N (r, x) 0 = Path.refl y :=
  (family γ α N (r, x)).source

/-- Both original outer-loop endpoints remain at the constant inner loop. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrismCore.lean:114"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
theorem family_one (r : unitInterval) (x : X) : family γ α N (r, x) 1 = Path.refl y :=
  (family γ α N (r, x)).target

end Topology.LoopNormalizationPrism
