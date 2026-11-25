/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.Topology.Path.SpanReassociation
public import Colib.Topology.Path.EvaluationFactorExtraction
public import Colib.Topology.Path.AssociatorEvaluation

/-!
# Whole target words determine the prescribed five-path reassociation

The pointwise theorem requires only the stated topologies and an arbitrary evaluation
function. For two continuous maps into a common space, equality of the whole target
words recovers each leaf using `EvaluationFactorExtraction` and hence all three original
reassociation stages using the shared `EvaluationOperations`. No path or comparison
coordinate is changed.

Current consumer: the coefficient Bass span-composition full-reference beta seam.
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

/-- Every actual reassociation clock is preserved by pointwise evaluation of its five leaves. -/
theorem spanReassociation (f : X → Y)
    (P : Path a b) (Q : Path b c) (T : Path c d) (U : Path d e) (V : Path e z)
    (P' : Path a' b') (Q' : Path b' c') (T' : Path c' d')
    (U' : Path d' e') (V' : Path e' z')
    (hP : ∀ s, f (P s) = P' s) (hQ : ∀ s, f (Q s) = Q' s)
    (hT : ∀ s, f (T s) = T' s) (hU : ∀ s, f (U s) = U' s)
    (hV : ∀ s, f (V s) = V' s) (r s : I) :
    f (Path.Homotopy.spanReassociation P Q T U V (r, s)) =
      Path.Homotopy.spanReassociation P' Q' T' U' V' (r, s) := by
  exact comparison_trans f _ _ _ _
    (comparison_hcomp f _ _ _ _ (fun _ s ↦ hP s)
      (transAssoc f Q (T.trans U) V Q' (T'.trans U') V' hQ
        (path_trans f T U T' U' hT hU) hV))
    (comparison_trans f _ _ _ _
      (comparison_hcomp f _ _ _ _ (fun _ s ↦ hP s)
        (comparison_hcomp f _ _ _ _ (fun _ s ↦ hQ s)
          (transAssoc f T U V T' U' V' hT hU hV)))
      (comparison_symm f _ _
        (transAssoc f P Q (T.trans (U.trans V)) P' Q' (T'.trans (U'.trans V'))
          hP hQ (path_trans f T (U.trans V) T' (U'.trans V') hT
            (path_trans f U V U' V' hU hV))))) r s

/-- The complete target word supplies its five unchanged leaves at their literal dyadic cuts. -/
theorem spanReassociation_of_target (f : C(X, Z)) (g : C(Y, Z))
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
