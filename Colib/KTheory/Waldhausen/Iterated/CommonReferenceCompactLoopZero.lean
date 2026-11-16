/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceCompactStageZero
public import Colib.Topology.Realization.Constant

/-!
# Compact common-reference evaluation on the original loop K-space

The actual pointed stage-zero evaluator acts on the original loop with the carrier point
held fixed. The loop coordinate is independent of every compact carrier parameter.
-/
@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology unitInterval

universe u v

namespace CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve

open SmallWaldhausenCategory

variable {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W)

/-- The stage-zero section uses the original zero vertex and the unchanged whole nerve. -/
def stageZeroPointSection :
    nerve (Codiscrete (Node F)) ⟶ (stages 0).obj V ⊗ nerve (Codiscrete (Node F)) :=
  lift (SSet.const (stageVertex 0 V)) (𝟙 _)

/-- All the original nerve simplices fix the chosen stage-zero vertex, as a whole map. -/
theorem stageZeroPointSection_comp :
    stageZeroPointSection F ≫ stageZeroTransformation F = SSet.const (stageVertex 0 W) := by
  ext n z : 3
  let N := nerve (Codiscrete (Node F))
  let p₀ : (Δ[0] : SSet.{u}) _⦋0⦌ := SSet.stdSimplex.objEquiv.symm (𝟙 ⦋0⦌)
  let p : (Δ[0] : SSet.{u}).obj n := (SSet.const (X := N) p₀).app n z
  let q : ((Δ[0] : SSet.{u}) ⊗ Δ[n.unop.len]).obj n := (p, ⟨𝟙 n.unop⟩)
  let φ := weakNaturalTransformationSimplex V.obj.waldhausen W.obj.waldhausen
    (z ⋙ diagram F) (fun i ↦ (z.obj i).as.1.hom.isExact)
    (fun _ _ f x ↦ diagram_weak F (z.map f) x)
  have fixed := weakNaturalTransformationSimplex_fixed_zero
    V.obj.waldhausen W.obj.waldhausen
    (z ⋙ diagram F) (fun i ↦ (z.obj i).as.1.hom.isExact)
    (fun _ _ f x ↦ diagram_weak F (z.map f) x) (fun i ↦ (z.obj i).as.1.property)
  have eval := congrArg
    (fun a : (Δ[0] : SSet.{u}) ⊗ Δ[n.unop.len] ⟶ (stages 0).obj W ↦ a.app n q) fixed
  have hv (D : WideSubcategory preservesZero.{u}) :
      (SSet.const (X := N) (stageVertex 0 D)).app n z =
        (SSet.yonedaEquiv.symm (stageVertex 0 D)).app n p := by
    have hc : (SSet.const (X := N) (stageVertex 0 D)) =
        SSet.const p₀ ≫ SSet.yonedaEquiv.symm (stageVertex 0 D) := by
      rw [SSet.const_comp, SSet.yonedaEquiv.apply_symm_apply]
    exact congrArg (fun a : N ⟶ (stages 0).obj D ↦ a.app n z) hc
  change φ.app n ((SSet.const (X := N) (stageVertex 0 V)).app n z, ⟨𝟙 n.unop⟩) =
    (SSet.const (X := N) (stageVertex 0 W)).app n z
  rw [hv V, hv W]
  exact eval

/-- The realized section retains the chosen zero point and the original carrier coordinate. -/
theorem stageZeroPointSection_comparison (y : |nerve (Codiscrete (Node F))|) :
    SSet.ProductRealization.comparison ((stages 0).obj V) (nerve (Codiscrete (Node F)))
        (SSet.toTop.map (stageZeroPointSection F) y) = (stagePoint 0 V, y) := by
  change (SSet.toTop.map (fst _ _) (SSet.toTop.map (stageZeroPointSection F) y),
    SSet.toTop.map (snd _ _) (SSet.toTop.map (stageZeroPointSection F) y)) = _
  apply _root_.Prod.ext
  · change (SSet.toTop.map (stageZeroPointSection F) ≫ SSet.toTop.map (fst _ _)) y = _
    rw [← CategoryTheory.Functor.map_comp]
    simpa only [stageZeroPointSection, lift_fst] using
      (SSet.realization_const_apply (stageVertex 0 V) y)
  · change (SSet.toTop.map (stageZeroPointSection F) ≫ SSet.toTop.map (snd _ _)) y = y
    rw [← CategoryTheory.Functor.map_comp, stageZeroPointSection, lift_snd,
      CategoryTheory.Functor.map_id]
    rfl

variable {T U : Type v} [TopologicalSpace T] [TopologicalSpace U]
  [CompactSpace T] [CompactSpace U]

/-- The exact compact stage-zero evaluator fixes the original realized point. -/
theorem compactStageZeroFamily_point
    (p : C(T, |nerve (Codiscrete (Node F))|)) (t : T) :
    compactStageZeroFamily F p (t, stagePoint 0 V) = stagePoint 0 W := by
  have h := SSet.ProductRealization.compactRightEvaluation_eq_of_comparison
    (stageZeroTransformation F) p t (stagePoint 0 V)
    (SSet.toTop.map (stageZeroPointSection F) (p t)) (stageZeroPointSection_comparison F (p t))
  change compactStageZeroFamily F p (t, stagePoint 0 V) = _ at h
  refine h.trans ?_
  change (SSet.toTop.map (stageZeroPointSection F) ≫ SSet.toTop.map
    (stageZeroTransformation F)) (p t) = _
  rw [← CategoryTheory.Functor.map_comp, stageZeroPointSection_comp]
  exact SSet.realization_const_apply (stageVertex 0 W) (p t)

/-- Evaluate the actual original loop at its own coordinate against the literal compact point. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/CommonReferenceNerveCompactFamily.lean:57-69"
  "adaptation" "Compact evaluation on the actual original loop K-space."]
def compactLoopZeroFamily (p : C(T, |nerve (Codiscrete (Node F))|)) :
    C(T × (prespectrum V).space 0, (prespectrum W).space 0) where
  toFun z :=
    { toFun s := compactStageZeroFamily F p (z.1, z.2 s)
      continuous_toFun := by fun_prop
      source' := by rw [Path.source]; exact compactStageZeroFamily_point F p z.1
      target' := by rw [Path.target]; exact compactStageZeroFamily_point F p z.1 }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z : (T × Path (stagePoint 0 V) (stagePoint 0 V)) × unitInterval ↦
      compactStageZeroFamily F p (z.1.1, z.1.2 z.2))
    fun_prop

/-- The original independent loop clock is not moved by the compact carrier. -/
theorem compactLoopZeroFamily_apply (p : C(T, |nerve (Codiscrete (Node F))|)) (t : T)
    (γ : Path (stagePoint 0 V) (stagePoint 0 V)) (s : unitInterval) :
    (show Path (stagePoint 0 W) (stagePoint 0 W) from compactLoopZeroFamily F p (t, γ)) s =
      compactStageZeroFamily F p (t, γ s) := rfl

/-- Different compact carriers agreeing at one point preserve the entire same loop. -/
theorem compactLoopZeroFamily_of_point_eq
    (p : C(T, |nerve (Codiscrete (Node F))|))
    (q : C(U, |nerve (Codiscrete (Node F))|)) (t : T) (s : U) (h : p t = q s)
    (γ : Path (stagePoint 0 V) (stagePoint 0 V)) :
    compactLoopZeroFamily F p (t, γ) = compactLoopZeroFamily F q (s, γ) := by
  apply Path.ext
  funext r
  exact compactStageZeroFamily_of_point_eq F p q t s h (γ r)

end CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve
