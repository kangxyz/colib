module

public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceCompactStage

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open scoped Simplicial Topology unitInterval

universe u

namespace ColibTest.CommonReferenceCompactStage

variable {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W)

/-- At arbitrary original stage, matching the carrier recovers the whole cubic chain. -/
theorem cube_chain (r : ℕ) (p : C((Fin 3 → unitInterval), |nerve (Codiscrete (Node F))|))
    (a b c : unitInterval) (K : Fin 4 ⥤ Codiscrete (Node F)) (z : |(Δ[3] : SSet.{u})|)
    (h : SSet.toTop.map (chainMap F K) z = p ![a, b, c]) (x : stageSpace r V) :
    compactStageFamily F r p (![a, b, c], x) = stageSimplexRealization r (chain F K) (x, z) :=
  compactStageFamily_eq_chain F r p K _ z h x

/-- Degree zero remains the earlier native literal evaluation. -/
theorem cube_stage_zero (p : C((Fin 3 → unitInterval), |nerve (Codiscrete (Node F))|)) :
    compactStageFamily F 0 p = compactStageZeroFamily F p :=
  compactStageFamily_zero F p

end ColibTest.CommonReferenceCompactStage
