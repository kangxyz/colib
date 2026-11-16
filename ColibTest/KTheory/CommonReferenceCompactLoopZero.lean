module

public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceCompactLoopZero

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open scoped Simplicial Topology unitInterval

universe u

namespace ColibTest.CommonReferenceCompactLoopZero

variable {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W)

/-- A cube carrier and the fourth independent clock evaluate the literal input loop. -/
theorem cube_loop_coordinate (p : C((Fin 3 → unitInterval), |nerve (Codiscrete (Node F))|))
    (r s t z : unitInterval) (γ : Path (stagePoint 0 V) (stagePoint 0 V)) :
    (show Path (stagePoint 0 W) (stagePoint 0 W) from
      compactLoopZeroFamily F p (![r, s, t], γ)) z =
      compactStageZeroFamily F p (![r, s, t], γ z) :=
  compactLoopZeroFamily_apply F p _ γ z

/-- A genuine matching face recovers the whole original loop, not only its endpoint. -/
theorem cube_face_loop (p : C((Fin 3 → unitInterval), |nerve (Codiscrete (Node F))|))
    (q : C(unitInterval × unitInterval, |nerve (Codiscrete (Node F))|))
    (s t : unitInterval) (h : p ![0, s, t] = q (s, t))
    (γ : Path (stagePoint 0 V) (stagePoint 0 V)) :
    compactLoopZeroFamily F p (![0, s, t], γ) = compactLoopZeroFamily F q ((s, t), γ) :=
  compactLoopZeroFamily_of_point_eq F p q _ _ h γ

end ColibTest.CommonReferenceCompactLoopZero
