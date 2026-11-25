/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.Topology.Path.SpanReassociationNaturality

/-!
# Reassociation from a whole target word under arbitrary evaluation

The evaluator on the source carrier need not be continuous. The target is evaluated by a
continuous map, so each target leaf remains a genuine path. This is useful for compact-family
realization without asserting continuity of an evaluator on the entire reference nerve.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Topology unitInterval
universe u v w
namespace Path.Evaluation
variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {a b c d e z : X} {a' b' c' d' e' z' : Y}

/-- The complete target word supplies its five unchanged leaves at their literal dyadic cuts. -/
theorem spanReassociation_of_target_function (f : X → Z) (g : C(Y, Z))
    (P : Path a b) (Q : Path b c) (T : Path c d) (U : Path d e) (V : Path e z)
    (P' : Path a' b') (Q' : Path b' c') (T' : Path c' d')
    (U' : Path d' e') (V' : Path e' z')
    (h : ∀ t : I, f (((P.trans Q).trans (T.trans (U.trans V))) t) =
      g (((P'.trans Q').trans (T'.trans (U'.trans V'))) t)) (r s : I) :
    f (Path.Homotopy.spanReassociation P Q T U V (r, s)) =
      g (Path.Homotopy.spanReassociation P' Q' T' U' V' (r, s)) := by
  have hword (t : I) : f (((P.trans Q).trans (T.trans (U.trans V))) t) =
      (((P'.map g.continuous).trans (Q'.map g.continuous)).trans
        ((T'.map g.continuous).trans
          ((U'.map g.continuous).trans (V'.map g.continuous)))) t := by
    simpa only [← Path.map_trans, Path.map_coe, Function.comp_apply] using h t
  have hPQ := left_factor f (P.trans Q) (T.trans (U.trans V))
    ((P'.map g.continuous).trans (Q'.map g.continuous))
    ((T'.map g.continuous).trans ((U'.map g.continuous).trans (V'.map g.continuous))) hword
  have hTUV := right_factor f (P.trans Q) (T.trans (U.trans V))
    ((P'.map g.continuous).trans (Q'.map g.continuous))
    ((T'.map g.continuous).trans ((U'.map g.continuous).trans (V'.map g.continuous))) hword
  have hUV := right_factor f T (U.trans V) (T'.map g.continuous)
    ((U'.map g.continuous).trans (V'.map g.continuous)) hTUV
  have hP := left_factor f P Q (P'.map g.continuous) (Q'.map g.continuous) hPQ
  have hQ := right_factor f P Q (P'.map g.continuous) (Q'.map g.continuous) hPQ
  have hT := left_factor f T (U.trans V) (T'.map g.continuous)
    ((U'.map g.continuous).trans (V'.map g.continuous)) hTUV
  have hU := left_factor f U V (U'.map g.continuous) (V'.map g.continuous) hUV
  have hV := right_factor f U V (U'.map g.continuous) (V'.map g.continuous) hUV
  exact (spanReassociation f P Q T U V (P'.map g.continuous) (Q'.map g.continuous)
    (T'.map g.continuous) (U'.map g.continuous) (V'.map g.continuous)
    hP hQ hT hU hV r s).trans
    (spanReassociation g P' Q' T' U' V' (P'.map g.continuous) (Q'.map g.continuous)
      (T'.map g.continuous) (U'.map g.continuous) (V'.map g.continuous)
      (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) r s).symm

end Path.Evaluation
