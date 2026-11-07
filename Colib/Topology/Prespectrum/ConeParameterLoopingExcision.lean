/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.ConeParameterLoopingStable
public import Colib.Topology.Prespectrum.ConeLinearExcision
public import Colib.Topology.Prespectrum.ParameterLoopingPointHEP

/-!
# Genuine loop-cofiber excision from original linear connectivity growth

An actual parameter loop loses exactly one degree of all-point vanishing. Its chosen-point
HEP follows from the proved compact-open loop construction applied to the original closed
point with HEP. These facts discharge both finite-excision inputs of the canonical loop-cofiber
comparison using the unchanged cone-to-fiber maps. The linear offset is increased by one.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/ConeParameterLoopingExcision.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original levelwise T1, point-HEP and all-point growth hypotheses are
retained, with the actual loop-space degree loss and one-larger linear offset. -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum
variable {E F : LoopPrespectrum.{u}} (f : E ⟶ F) (c : ℕ)
  [∀ m, T1Space (E.space m)] [∀ m, T1Space (F.space m)]
  (hE : ∀ m, TopCat.HomotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (E.point m))))
  (hF : ∀ m, TopCat.HomotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (F.point m))))
  (hπE : ∀ n x k, k < n + 2 →
    Subsingleton (HomotopyGroup.Pi k (E.space (n + c + 2)) x))
  (hπF : ∀ n x k, k < n + 2 →
    Subsingleton (HomotopyGroup.Pi k (F.space (n + c + 2)) x))

include hE hF hπE hπF

/-- The actual looped arrow satisfies original stable excision at the one-larger offset. -/
theorem parameterLoopingMap_coneFiber_isStableEquivalence_of_linearGrowth :
    IsStableEquivalence (mappingConeFiberComparison (parameterLoopingMap f)) := by
  apply mappingConeFiberComparison_isStableEquivalence_of_linearGrowth _ (c + 1)
  · intro n
    exact parameterLooping_point_homotopyExtensionProperty E _ isClosed_singleton (hE _)
  · intro n
    exact parameterLooping_point_homotopyExtensionProperty F _ isClosed_singleton (hF _)
  · intro n
    rw [show n + (c + 1) + 2 = (n + 1) + c + 2 by omega]
    intro γ k hk
    exact subsingleton_pi_loop_of_succ (E.point ((n + 1) + c + 2)) k
      (hπE (n + 1) (E.point ((n + 1) + c + 2)) (k + 1) (by omega)) γ
  · intro n
    rw [show n + (c + 1) + 2 = (n + 1) + c + 2 by omega]
    intro γ k hk
    exact subsingleton_pi_loop_of_succ (F.point ((n + 1) + c + 2)) k
      (hπF (n + 1) (F.point ((n + 1) + c + 2)) (k + 1) (by omega)) γ

/-- Original point topology and linear growth prove stability of the literal loop-cofiber map. -/
theorem mappingConeParameterLoopingComparison_isStableEquivalence_of_linearGrowth :
    IsStableEquivalence (mappingConeParameterLoopingComparison f) :=
  mappingConeParameterLoopingComparison_isStableEquivalence f
    (mappingConeFiberComparison_isStableEquivalence_of_linearGrowth f c
      (fun n ↦ hE (n + c + 2)) (fun n ↦ hF (n + c + 2)) hπE hπF)
    (parameterLoopingMap_coneFiber_isStableEquivalence_of_linearGrowth f c hE hF hπE hπF)

end Topology.LoopPrespectrum
