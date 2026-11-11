/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.Topology.Homotopy.HomotopyGroup.GenLoopNormalizedSelfTrack

/-! # Continuous families of the original inverse-prefix-normalized self-track

This file retains the actual cancellation word and proves continuity of the resulting
family. It extracts the original fixed-prefix construction; the moving-prefix prism
and comparison with a supplied null remain separate results.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u v
namespace Topology.LoopNormalizationPrism
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {y : Y}

/-- Curry a continuous zero-to-zero homotopy without any local-compactness assumption on X. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrismCore.lean:41"
  "adaptation" "Original continuous inverse-prefix cancellation family"]
def basedFamily (H : (ContinuousMap.const X (Path.refl y)).Homotopy
    (ContinuousMap.const X (Path.refl y))) : C(X, Path (Path.refl y) (Path.refl y)) where
  toFun x := H.evalAt x
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact H.continuous.comp (continuous_snd.prodMk continuous_fst)

/-- Evaluation retains the original two half intervals of homotopy concatenation. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrismFaces.lean:27"
  "adaptation" "Original continuous inverse-prefix cancellation family"]
theorem evalAt_trans {f g h : C(X, Y)} (H : f.Homotopy g) (K : g.Homotopy h) (x : X) :
    (H.trans K).evalAt x = (H.evalAt x).trans (K.evalAt x) := by
  ext t
  simp only [ContinuousMap.Homotopy.evalAt_apply, ContinuousMap.Homotopy.trans_apply,
    Path.trans_apply]

/-- Evaluation retains the original reversed homotopy time. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrismFaces.lean:34"
  "adaptation" "Original continuous inverse-prefix cancellation family"]
theorem evalAt_symm {f g : C(X, Y)} (H : f.Homotopy g) (x : X) :
    H.symm.evalAt x = (H.evalAt x).symm := rfl

variable (γ : C(X, Path y y)) (α : γ.Homotopy γ)
  (N : γ.Homotopy (ContinuousMap.const X (Path.refl y)))

/-- The actual based-loop family obtained by conjugating with the supplied null. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrismFaces.lean:51"
  "adaptation" "Original continuous inverse-prefix cancellation family"]
def nullConjugate : C(X, Path (Path.refl y) (Path.refl y)) :=
  basedFamily (N.symm.trans (α.trans N))

/-- The full null-conjugate retains the original nesting and clocks. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrismFaces.lean:55"
  "adaptation" "Original continuous inverse-prefix cancellation family"]
theorem nullConjugate_apply (x : X) :
    nullConjugate γ α N x = (N.evalAt x).symm.trans ((α.evalAt x).trans (N.evalAt x)) := by
  change (N.symm.trans (α.trans N)).evalAt x = _
  rw [evalAt_trans, evalAt_symm, evalAt_trans]

/-- The fixed inverse-prefixed base family. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrismFaces.lean:61"
  "adaptation" "Original continuous inverse-prefix cancellation family"]
def prefixBase : C(X, Path y y) :=
  ⟨fun x ↦ (γ x).symm.trans (γ x),
    Path.continuous_trans.comp ((Path.continuous_symm.comp γ.continuous).prodMk γ.continuous)⟩

/-- The actual original inverse-prefixed self-track. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrismFaces.lean:66"
  "adaptation" "Original continuous inverse-prefix cancellation family"]
def prefixTrack : (prefixBase γ).Homotopy (prefixBase γ) where
  toFun z := (γ z.2).symm.trans (α z)
  continuous_toFun := Path.continuous_trans.comp
    ((Path.continuous_symm.comp (γ.continuous.comp continuous_snd)).prodMk α.continuous)
  map_zero_left x := by simp [prefixBase]
  map_one_left x := by simp [prefixBase]

/-- The original cancellation at every parameter of the initial family. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrismFaces.lean:74"
  "adaptation" "Original continuous inverse-prefix cancellation family"]
def originalCancellation : (prefixBase γ).Homotopy (ContinuousMap.const X (Path.refl y)) where
  toFun z := loopInversePrefixCancellation (γ z.2) z.1
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z : (unitInterval × X) × unitInterval ↦
      γ z.1.2 (unitInterval.symm ⟨Path.Homotopy.reflTransSymmAux
        (unitInterval.symm z.1.1, z.2), Path.Homotopy.reflTransSymmAux_mem_I _⟩))
    fun_prop
  map_zero_left x := (loopInversePrefixCancellation (γ x)).source
  map_one_left x := (loopInversePrefixCancellation (γ x)).target

/-- A continuous family of the original specified inverse-prefix normalizations. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrismFaces.lean:86"
  "adaptation" "Original continuous inverse-prefix cancellation family"]
def normalized : C(X, Path (Path.refl y) (Path.refl y)) :=
  nullConjugate (prefixBase γ) (prefixTrack γ α) (originalCancellation γ)

/-- The continuous family is literally the library's original normalized self-track. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrismFaces.lean:90"
  "adaptation" "Original continuous inverse-prefix cancellation family"]
theorem normalized_apply (x : X) :
    normalized γ α x = loopNormalizedSelfTrack (γ x) (α.evalAt x) := by
  have h : (prefixTrack γ α).evalAt x =
      ((α.evalAt x).map (loopLeftTranslationEquiv (γ x).symm).continuous).cast
        (loopLeftTranslationEquiv_apply _ _).symm
        (loopLeftTranslationEquiv_apply _ _).symm := by
    apply Path.ext
    funext t
    exact (loopLeftTranslationEquiv_apply (γ x).symm (α (t, x))).symm
  rw [normalized, nullConjugate_apply, h]
  rfl

end Topology.LoopNormalizationPrism
