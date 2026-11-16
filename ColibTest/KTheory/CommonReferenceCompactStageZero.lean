module

public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceCompactStageZero

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen MonoidalCategory
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve
open SmallWaldhausenCategory
open scoped Simplicial Topology unitInterval

universe u

namespace ColibTest.CommonReferenceCompactStageZero

variable {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W)

/-- The original three-parameter carrier is evaluated against the actual stage-zero input. -/
theorem cube_point (p : C((Fin 3 → unitInterval), |nerve (Codiscrete (Node F))|))
    (r s t : unitInterval) (x : stageSpace 0 V)
    (q : |(stages 0).obj V ⊗ nerve (Codiscrete (Node F))|)
    (h : SSet.ProductRealization.comparison _ _ q = (x, p ![r, s, t])) :
    compactStageZeroFamily F p (![r, s, t], x) =
      SSet.toTop.map (stageZeroTransformation F) q :=
  SSet.ProductRealization.compactRightEvaluation_eq_of_comparison
    (stageZeroTransformation F) p _ x q h

/-- Restricting the parameter face does not change the evaluated carrier point. -/
theorem cube_zero_face (p : C((Fin 3 → unitInterval), |nerve (Codiscrete (Node F))|))
    (q : C(unitInterval × unitInterval, |nerve (Codiscrete (Node F))|))
    (s t : unitInterval) (h : p ![0, s, t] = q (s, t)) (x : stageSpace 0 V) :
    compactStageZeroFamily F p (![0, s, t], x) = compactStageZeroFamily F q ((s, t), x) :=
  compactStageZeroFamily_of_point_eq F p q _ _ h x

end ColibTest.CommonReferenceCompactStageZero
