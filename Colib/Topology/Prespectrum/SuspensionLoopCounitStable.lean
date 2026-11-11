/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.PointFiberIso
public import Colib.Topology.Prespectrum.PointHEP
public import Colib.Topology.Prespectrum.ConeParameterLoopingExcision
public import Colib.Topology.Prespectrum.ConeDescStableEquivalence

/-! # Stable counit from the original cone excision

Actual cone-to-fiber excision, point HEP and all-point linear growth prove stability of
the original evaluation counit through the genuine point-fiber isomorphism.
-/
@[expose] public noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
universe u v w
namespace Topology.LoopPrespectrum

/-- Original excision makes the unchanged suspension-loop evaluation counit stable. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/SuspensionLoopCounitStable.lean:26"
  "adaptation" "Original actual finite-stage topology and full all-point growth bounds."]
theorem suspensionLoopCounit_isStableEquivalence (E : LoopPrespectrum.{u})
    (he : IsStableEquivalence
      (mappingConeFiberComparison (zeroHom (parameterLooping E) pointPrespectrum))) :
    IsStableEquivalence (suspensionLoopCounit E) := by
  apply mappingConeDesc_isStableEquivalence _ _ _ he
  rw [loopEvaluationHomotopy_fiberLift]
  intro d
  infer_instance

/-- All-point linear growth and the original point topology discharge the actual excision. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/SuspensionLoopCounitStable.lean:36"
  "adaptation" "Original actual finite-stage topology and full all-point growth bounds."]
theorem suspensionLoopCounit_isStableEquivalence_of_linearGrowth
    (E : LoopPrespectrum.{u}) (c : ℕ) [∀ n, T1Space (E.space n)]
    (hE : ∀ n, TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (E.point n))))
    (hπ : ∀ n x k, k < n + 2 →
      Subsingleton (HomotopyGroup.Pi k (E.space (n + c + 2)) x)) :
    IsStableEquivalence (suspensionLoopCounit E) := by
  apply suspensionLoopCounit_isStableEquivalence
  apply mappingConeFiberComparison_isStableEquivalence_of_linearGrowth _ (c + 1)
  · intro n
    exact parameterLooping_point_homotopyExtensionProperty E _ isClosed_singleton (hE _)
  · intro n
    exact pointPrespectrum_point_homotopyExtensionProperty _
  · intro n
    rw [show n + (c + 1) + 2 = (n + 1) + c + 2 by omega]
    intro γ k hk
    exact Topology.subsingleton_pi_loop_of_succ (E.point ((n + 1) + c + 2)) k
      (hπ (n + 1) (E.point _) (k + 1) (by omega)) γ
  · intro n x k _hk
    exact Topology.subsingleton_pi_of_contractible k PUnit.{u + 1} x

/-- The actual parameter loop of the same counit is stable in the direction used by TT. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/SuspensionLoopCounitStable.lean:58"
  "adaptation" "Original actual finite-stage topology and full all-point growth bounds."]
theorem parameterLooping_suspensionLoopCounit_isStableEquivalence
    (E : LoopPrespectrum.{u}) (he : IsStableEquivalence (suspensionLoopCounit E)) :
    IsStableEquivalence (parameterLoopingMap (suspensionLoopCounit E)) :=
  parameterLoopingMap_isStableEquivalence _ he

end Topology.LoopPrespectrum
