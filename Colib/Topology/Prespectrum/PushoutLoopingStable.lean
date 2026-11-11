/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.PushoutLooping
public import Colib.Topology.Prespectrum.PushoutStableEquivalence
public import Colib.Topology.Prespectrum.HomotopyPushoutSeparation
public import Colib.Topology.Prespectrum.PushoutLinearExcision
public import Colib.Topology.Prespectrum.ConeParameterLoopingExcision
public import Colib.Topology.Prespectrum.ParameterLoopingStableEquivalence

/-!
# Reconstructed stability of the pushout-loop comparison

The proof uses the original forward cone square, actual linear growth, and signed cofiber
sequences. This is an adopted independent reconstruction against the identified baseline.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.HomotopyPushout.Looping

/-- Actual chosen-point homotopy extension in every level. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutLoopingStable.lean:31"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
abbrev HEP (E : LoopPrespectrum.{u}) := ∀ n, TopCat.HomotopyExtensionProperty
  (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (E.point n)))

/-- The original all-point linear connectivity range. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutLoopingStable.lean:35"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
abbrev Growth (E : LoopPrespectrum.{u}) (c : ℕ) := ∀ n x k, k < n + 2 →
  Subsingleton (HomotopyGroup.Pi k (E.space (n + c + 2)) x)

/-- Looping retains actual point HEP. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutLoopingStable.lean:39"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem loop_hep (E : LoopPrespectrum.{u}) [∀ n, T1Space (E.space n)]
    (hE : HEP E) : HEP (parameterLooping E) := by
  intro n
  exact parameterLooping_point_homotopyExtensionProperty E n isClosed_singleton (hE n)

/-- Looping loses one degree in the original connectivity range. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutLoopingStable.lean:45"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem loop_growth (E : LoopPrespectrum.{u}) (c : ℕ) (hE : Growth E c) :
    Growth (parameterLooping E) (c + 1) := by
  intro n
  rw [show n + (c + 1) + 2 = (n + 1) + c + 2 by omega]
  intro γ k hk
  exact subsingleton_pi_loop_of_succ (E.point ((n + 1) + c + 2)) k
    (hE (n + 1) (E.point ((n + 1) + c + 2)) (k + 1) (by omega)) γ

variable {A B C : LoopPrespectrum.{u}} (f : A ⟶ B) (g : A ⟶ C)

/-- The actual pushout inherits chosen-point HEP. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutLoopingStable.lean:56"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem span_hep (hA : HEP A) (hB : HEP B) (hC : HEP C) :
    HEP (prespectrum f g) := fun n =>
  point_homotopyExtensionProperty f g n (hA n) (hB n) (hC n)

/-- The actual pushout inherits the original all-point connectivity range. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutLoopingStable.lean:61"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem span_growth (c : ℕ) (hA : HEP A) (hB : HEP B) (hC : HEP C)
    (hπA : Growth A c) (hπB : Growth B c) (hπC : Growth C c) :
    Growth (prespectrum f g) c := by
  intro n x k hk
  exact homotopyGroup_subsingleton f g (n + c + 2) n
    (hA _) (hB _) (hC _) (hπA n) (hπB n) (hπC n) x k hk

/-- The identity and the actual comparison form the square of right inclusions. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutLoopingStable.lean:69"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def rightSquare : Arrow.mk (inr (parameterLoopingMap f) (parameterLoopingMap g)) ⟶
    Arrow.mk (parameterLoopingMap (inr f g)) :=
  Arrow.homMk (𝟙 _) (comparison f g) (by simpa using (comparison_right f g).symm)

/-- The original forward cone square retains the whole overlap and cone heights. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutLoopingStable.lean:74"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem coneSquare :
    mappingConeMap (rightSquare f g) ≫
        mappingConeParameterLoopingComparison (inr f g) ≫
          parameterLoopingMap (rightConeCollapse f g) =
      rightConeCollapse (parameterLoopingMap f) (parameterLoopingMap g) ≫
        mappingConeParameterLoopingComparison f := by
  apply Hom.ext
  funext n
  apply ReducedMappingCone.hom_ext
  · intro z
    apply Path.ext
    funext t
    induction z using Quot.inductionOn with
    | h z =>
      cases z with
      | inl z => cases z <;> rfl
      | inr z => rfl
  · intro z
    apply Path.ext
    funext t
    rfl

/-- Actual point topology and linear growth imply stability of the original comparison. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutLoopingStable.lean:97"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem comparison_isStableEquivalence_of_linearGrowth (c : ℕ)
    [∀ n, T1Space (A.space n)] [∀ n, T1Space (B.space n)] [∀ n, T1Space (C.space n)]
    (hA : HEP A) (hB : HEP B) (hC : HEP C)
    (hπA : Growth A c) (hπB : Growth B c) (hπC : Growth C c) :
    IsStableEquivalence (comparison f g) := by
  have hP := span_hep f g hA hB hC
  have hπP := span_growth f g c hA hB hC hπA hπB hπC
  have hν := mappingConeParameterLoopingComparison_isStableEquivalence_of_linearGrowth
    (inr f g) c hC hP hπC hπP
  have hk : IsStableEquivalence (rightConeCollapse f g) :=
    isStableEquivalence_of_positiveLevel _ (fun n =>
      rightConeCollapse_level_isWeakHomotopyEquivalence f g (n + 1) (hA _) (hB _) (hC _))
  have hΩk := parameterLoopingMap_isStableEquivalence _ hk
  have hk' : IsStableEquivalence
      (rightConeCollapse (parameterLoopingMap f) (parameterLoopingMap g)) :=
    isStableEquivalence_of_positiveLevel _ (fun n =>
      rightConeCollapse_level_isWeakHomotopyEquivalence _ _ (n + 1)
        (loop_hep A hA _) (loop_hep B hB _) (loop_hep C hC _))
  have hνf := mappingConeParameterLoopingComparison_isStableEquivalence_of_linearGrowth
    f c hA hB hπA hπB
  have hcomp := hk'.comp hνf
  rw [← coneSquare f g] at hcomp
  have hcone : IsStableEquivalence (mappingConeMap (rightSquare f g)) := by
    intro d
    let := hν d
    let := hΩk d
    let : IsIso ((stableHomotopyFunctor d).map (mappingConeMap (rightSquare f g)) ≫
        ((stableHomotopyFunctor d).map (mappingConeParameterLoopingComparison (inr f g)) ≫
          (stableHomotopyFunctor d).map (parameterLoopingMap (rightConeCollapse f g)))) := by
      simpa only [Functor.map_comp] using hcomp d
    exact IsIso.of_isIso_comp_right
      ((stableHomotopyFunctor d).map (mappingConeMap (rightSquare f g)))
      ((stableHomotopyFunctor d).map (mappingConeParameterLoopingComparison (inr f g)) ≫
        (stableHomotopyFunctor d).map (parameterLoopingMap (rightConeCollapse f g)))
  apply right_isStableEquivalence_of_coneMap (rightSquare f g) _ _ _ hcone
  · exact inr_coneFiber_isStableEquivalence_of_linearGrowth _ _ (c + 1)
      (fun n => loop_hep A hA _) (fun n => loop_hep B hB _) (fun n => loop_hep C hC _)
      (loop_growth A c hπA) (loop_growth B c hπB) (loop_growth C c hπC)
  · exact parameterLoopingMap_coneFiber_isStableEquivalence_of_linearGrowth
      (inr f g) c hC hP hπC hπP
  · intro d
    change IsIso ((stableHomotopyFunctor d).map (𝟙 (parameterLooping C)))
    infer_instance

end Topology.LoopPrespectrum.HomotopyPushout.Looping
