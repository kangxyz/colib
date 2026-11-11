/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.Loop.NormalizationPrismFaces

/-!
# A parameterized normalization prism for original loop-space self-tracks

The original inverse-prefix normalization is continuously homotopic to conjugation by any
specified continuous null of the component family. The construction first removes the exact
initial pause, follows the moving-prefix core, and finally removes the terminal pause and
constant inner prefix. All input parameters and both loop coordinates stay independent.

This is a homotopy into the space of based double loops. Compatibility with a prespectrum
structure requires a separate certificate when that structure interchanges the loop directions.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u v
namespace Topology.LoopNormalizationPrism
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {y : Y}

/-- Retain a homotopy while adjoining an independent prism parameter. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrism.lean:31"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
def liftTrack {f g : C(X, Y)} (H : f.Homotopy g) :
    (f.comp (ContinuousMap.snd : C(unitInterval × X, X))).Homotopy
      (g.comp (ContinuousMap.snd : C(unitInterval × X, X))) where
  toFun z := H (z.1, z.2.2)
  continuous_toFun := H.continuous.comp
    (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
  map_zero_left x := H.apply_zero x.2
  map_one_left x := H.apply_one x.2

/-- Remove an initial pause uniformly in every return path of a homotopy. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrism.lean:41"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
def delayLeft {f g : C(X, Y)} (H : f.Homotopy g) :
    (f.comp (ContinuousMap.snd : C(unitInterval × X, X))).Homotopy
      (g.comp (ContinuousMap.snd : C(unitInterval × X, X))) where
  toFun z := Path.delayReflLeft z.2.1 (H.evalAt z.2.2) z.1
  continuous_toFun := by
    change Continuous (fun z : unitInterval × (unitInterval × X) ↦
      H (unitInterval.symm (unitInterval.qRight (unitInterval.symm z.1, z.2.1)), z.2.2))
    fun_prop
  map_zero_left x := (Path.delayReflLeft x.1 (H.evalAt x.2)).source
  map_one_left x := (Path.delayReflLeft x.1 (H.evalAt x.2)).target

/-- Remove a terminal pause uniformly in every return path of a homotopy. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrism.lean:53"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
def delayRight {f g : C(X, Y)} (H : f.Homotopy g) :
    (f.comp (ContinuousMap.snd : C(unitInterval × X, X))).Homotopy
      (g.comp (ContinuousMap.snd : C(unitInterval × X, X))) where
  toFun z := Path.delayReflRight z.2.1 (H.evalAt z.2.2) z.1
  continuous_toFun := by
    change Continuous (fun z : unitInterval × (unitInterval × X) ↦
      H (unitInterval.qRight (z.1, z.2.1), z.2.2))
    fun_prop
  map_zero_left x := (Path.delayReflRight x.1 (H.evalAt x.2)).source
  map_one_left x := (Path.delayReflRight x.1 (H.evalAt x.2)).target

variable (γ : C(X, Path y y)) (α : γ.Homotopy γ)
  (N : γ.Homotopy (ContinuousMap.const X (Path.refl y)))

/-- The zero face of the moving-prefix core as a continuous map. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrism.lean:68"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
def zeroFace : C(X, Path (Path.refl y) (Path.refl y)) :=
  (family γ α N).comp ⟨fun x ↦ (0, x), continuous_const.prodMk continuous_id⟩

/-- The one face of the moving-prefix core as a continuous map. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrism.lean:72"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
def oneFace : C(X, Path (Path.refl y) (Path.refl y)) :=
  (family γ α N).comp ⟨fun x ↦ (1, x), continuous_const.prodMk continuous_id⟩

/-- The continuous null-conjugation family with its initial pause shrinking. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrism.lean:76"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
def leftRemovalFamily : C(unitInterval × X, Path (Path.refl y) (Path.refl y)) :=
  basedFamily ((delayLeft (originalCancellation γ)).symm.trans
    ((liftTrack (prefixTrack γ α)).trans (delayLeft (originalCancellation γ))))

/-- Both occurrences of the initial pause use exactly the same reparametrization. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrism.lean:81"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
theorem leftRemovalFamily_apply (r : unitInterval) (x : X) :
    leftRemovalFamily γ α (r, x) =
      (Path.delayReflLeft r (loopInversePrefixCancellation (γ x))).symm.trans
        (((prefixTrack γ α).evalAt x).trans
          (Path.delayReflLeft r (loopInversePrefixCancellation (γ x)))) := by
  change (((delayLeft (originalCancellation γ)).symm.trans
    ((liftTrack (prefixTrack γ α)).trans
      (delayLeft (originalCancellation γ)))).evalAt (r, x)) = _
  rw [evalAt_trans, evalAt_symm, evalAt_trans]
  rfl

/-- Remove only the extra initial pause in the core's original cancellation word. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrism.lean:93"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
def leftRemoval : (zeroFace γ α N).Homotopy (normalized γ α) where
  toFun := leftRemovalFamily γ α
  continuous_toFun := (leftRemovalFamily γ α).continuous
  map_zero_left x := by
    change leftRemovalFamily γ α (0, x) = family γ α N (0, x)
    rw [leftRemovalFamily_apply, Path.delayReflLeft_zero, family_zero_face]
  map_one_left x := by
    rw [leftRemovalFamily_apply, Path.delayReflLeft_one]
    rw [normalized, nullConjugate_apply]
    rfl

/-- The actual moving-prefix core, with its two exact end words. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrism.lean:105"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
def coreHomotopy : (zeroFace γ α N).Homotopy (oneFace γ α N) where
  toFun := family γ α N
  continuous_toFun := (family γ α N).continuous
  map_zero_left _ := rfl
  map_one_left _ := rfl

/-- Conjugation after adding a constant prefix to each inner loop. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrism.lean:112"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
def leftConjugate : C(X, Path (Path.refl y) (Path.refl y)) :=
  basedFamily ((leftNull γ N).symm.trans ((leftTrack γ α).trans (leftNull γ N)))

/-- The continuous null-conjugation family with its terminal pause shrinking. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrism.lean:116"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
def rightRemovalFamily : C(unitInterval × X, Path (Path.refl y) (Path.refl y)) :=
  basedFamily ((delayRight (leftNull γ N)).symm.trans
    ((liftTrack (leftTrack γ α)).trans (delayRight (leftNull γ N))))

/-- Both occurrences of the terminal pause use exactly the same reparametrization. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrism.lean:121"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
theorem rightRemovalFamily_apply (r : unitInterval) (x : X) :
    rightRemovalFamily γ α N (r, x) =
      (Path.delayReflRight r ((leftNull γ N).evalAt x)).symm.trans
        (((leftTrack γ α).evalAt x).trans
          (Path.delayReflRight r ((leftNull γ N).evalAt x))) := by
  change (((delayRight (leftNull γ N)).symm.trans
    ((liftTrack (leftTrack γ α)).trans (delayRight (leftNull γ N)))).evalAt (r, x)) = _
  rw [evalAt_trans, evalAt_symm, evalAt_trans]
  rfl

/-- Remove only the terminal pauses from the one face of the core. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrism.lean:132"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
def rightRemoval : (oneFace γ α N).Homotopy (leftConjugate γ α N) where
  toFun := rightRemovalFamily γ α N
  continuous_toFun := (rightRemovalFamily γ α N).continuous
  map_zero_left x := by
    change rightRemovalFamily γ α N (0, x) = family γ α N (1, x)
    rw [rightRemovalFamily_apply, Path.delayReflRight_zero, family_one_face]
    rfl
  map_one_left x := by
    rw [rightRemovalFamily_apply, Path.delayReflRight_one]
    change _ = ((leftNull γ N).symm.trans
      ((leftTrack γ α).trans (leftNull γ N))).evalAt x
    rw [evalAt_trans, evalAt_symm, evalAt_trans]

/-- Remove the constant inner prefix throughout the complete outer conjugation word. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrism.lean:146"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
def innerRemovalWord : (ContinuousMap.const (unitInterval × X) (Path.refl y)).Homotopy
    (ContinuousMap.const (unitInterval × X) (Path.refl y)) where
  toFun z := Path.delayReflLeft z.2.1 (nullConjugate γ α N z.2.2 z.1)
  continuous_toFun := Path.continuous_delayReflLeft.comp
    ((continuous_fst.comp continuous_snd).prodMk
      (((nullConjugate γ α N).continuous.comp
        (continuous_snd.comp continuous_snd)).eval continuous_fst))
  map_zero_left x := by
    rw [(nullConjugate γ α N x.2).source]
    apply Path.ext
    funext s
    rfl
  map_one_left x := by
    rw [(nullConjugate γ α N x.2).target]
    apply Path.ext
    funext s
    rfl

/-- Remove the remaining constant inner prefix through its actual based reparametrization. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrism.lean:165"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
def innerRemoval : (leftConjugate γ α N).Homotopy (nullConjugate γ α N) where
  toFun := basedFamily (innerRemovalWord γ α N)
  continuous_toFun := (basedFamily (innerRemovalWord γ α N)).continuous
  map_zero_left x := by
    apply Path.ext
    funext t
    change Path.delayReflLeft 0 (nullConjugate γ α N x t) =
      ((leftNull γ N).symm.trans ((leftTrack γ α).trans (leftNull γ N))) (t, x)
    rw [Path.delayReflLeft_zero]
    change (Path.refl y).trans ((N.symm.trans (α.trans N)) (t, x)) = _
    simp only [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.symm_apply]
    split_ifs <;> rfl
  map_one_left x := by
    apply Path.ext
    funext t
    exact congrArg (fun p : Path y y ↦ p)
      (Path.delayReflLeft_one (nullConjugate γ α N x t))

/-- The complete continuous normalization prism, with the original words at both ends. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrism.lean:184"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
def normalizationHomotopy : (normalized γ α).Homotopy (nullConjugate γ α N) :=
  (leftRemoval γ α N).symm.trans
    ((coreHomotopy γ α N).trans ((rightRemoval γ α N).trans (innerRemoval γ α N)))

/-- Its zero face is the exact original inverse-prefix normalization. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrism.lean:189"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
theorem normalizationHomotopy_zero (x : X) :
    normalizationHomotopy γ α N (0, x) = loopNormalizedSelfTrack (γ x) (α.evalAt x) :=
  ((normalizationHomotopy γ α N).apply_zero x).trans (normalized_apply γ α x)

/-- Its one face retains the supplied null and the original three-piece conjugation clocks. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrism.lean:194"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
theorem normalizationHomotopy_one (x : X) :
    normalizationHomotopy γ α N (1, x) =
      (N.evalAt x).symm.trans ((α.evalAt x).trans (N.evalAt x)) :=
  ((normalizationHomotopy γ α N).apply_one x).trans (nullConjugate_apply γ α N x)

end Topology.LoopNormalizationPrism

attribute [colib_tag "COL-0552"]
  Topology.LoopNormalizationPrism.normalizationHomotopy
