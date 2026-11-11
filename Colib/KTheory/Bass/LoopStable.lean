/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.LoopFactor
public import Colib.Topology.Prespectrum.LoopTranspose
public import Colib.Topology.Prespectrum.PushoutLoopingStable
public import Colib.KTheory.Bass.ModelDiagramConnectivity

/-!
# Reconstructed finite-stage stability of Bass loop strength

The actual factorization through the cone comparison and double-loop transpose supplies
stability from genuine finite Model connectivity. This is an adopted independent reconstruction.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Topology.LoopPrespectrum
open Topology.LoopPrespectrum.HomotopyPushout.Looping
open CategoryTheory.Waldhausen.IteratedS
open scoped Topology unitInterval
universe u v w
namespace KTheory.Bass.LoopStable
open LoopFactor LoopStrength

/-- The forward cone strength is stable under actual corner topology and growth. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/LoopStable.lean:32"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem coneStrength_stable (S : Arrow (Arrow LoopPrespectrum.{w})) (c : ℕ)
    [∀ n, T1Space (S.left.left.space n)] [∀ n, T1Space (S.left.right.space n)]
    [∀ n, T1Space (S.right.left.space n)] [∀ n, T1Space (S.right.right.space n)]
    (hA : HEP S.left.left) (hB : HEP S.left.right)
    (hC : HEP S.right.left) (hD : HEP S.right.right)
    (hπA : Growth S.left.left c) (hπB : Growth S.left.right c)
    (hπC : Growth S.right.left c) (hπD : Growth S.right.right c) :
    IsStableEquivalence (coneStrength S) := by
  have hP := span_hep S.left.hom S.hom.left hA hB hC
  have hπP := span_growth S.left.hom S.hom.left c hA hB hC hπA hπB hπC
  have hPl := span_hep (parameterLoopingMap S.left.hom)
    (parameterLoopingMap S.hom.left) (loop_hep _ hA) (loop_hep _ hB) (loop_hep _ hC)
  have hπPl := span_growth (parameterLoopingMap S.left.hom)
    (parameterLoopingMap S.hom.left) (c + 1)
    (loop_hep _ hA) (loop_hep _ hB) (loop_hep _ hC)
    (loop_growth _ c hπA) (loop_growth _ c hπB) (loop_growth _ c hπC)
  let sq : Arrow.mk (StrictSquare.comparison (loopSquare S)) ⟶
      Arrow.mk (parameterLoopingMap (StrictSquare.comparison S)) :=
    Arrow.homMk (HomotopyPushout.Looping.comparison S.left.hom S.hom.left)
      (𝟙 _) (by simpa using (span_square S))
  have hf : IsStableEquivalence
      (mappingConeFiberComparison (StrictSquare.comparison (loopSquare S))) :=
    mappingConeFiberComparison_isStableEquivalence_of_linearGrowth _ (c + 1)
      (fun n => hPl _) (fun n => loop_hep _ hD _)
      hπPl (loop_growth _ c hπD)
  have ht : IsStableEquivalence
      (mappingConeFiberComparison (parameterLoopingMap (StrictSquare.comparison S))) :=
    parameterLoopingMap_coneFiber_isStableEquivalence_of_linearGrowth _ c hP hD hπP hπD
  have hl : IsStableEquivalence sq.left :=
    comparison_isStableEquivalence_of_linearGrowth S.left.hom S.hom.left c
      hA hB hC hπA hπB hπC
  have hr : IsStableEquivalence sq.right := by
    intro d
    change IsIso ((stableHomotopyFunctor d).map (𝟙 (parameterLooping S.right.right)))
    infer_instance
  exact (mappingConeMap_isStableEquivalence_of_excision sq hf ht hl hr).comp
    (mappingConeParameterLoopingComparison_isStableEquivalence_of_linearGrowth
      (StrictSquare.comparison S) c hP hD hπP hπD)

variable {C : Type u} [Category.{v} C]

/-- Equality of actual maps, including the final loop-coordinate transpose. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/LoopStable.lean:74"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem strength_factor (Q : C ⥤ Arrow (Arrow C))
    (F : C ⥤ LoopPrespectrum.{w}) (X : C) :
    strength Q F X =
      parameterLoopingMap (coneStrength (F.mapArrow.mapArrow.obj (Q.obj X))) ≫
        (LoopTranspose.iso
          (mappingCone (StrictSquare.comparison (F.mapArrow.mapArrow.obj (Q.obj X))))).hom := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro γ
  apply Path.ext
  funext r
  apply Path.ext
  funext t
  exact strength_factor_value F Q X n γ r t

/-- The original loop strength is stable under genuine diagram connectivity. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/LoopStable.lean:91"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem strength_stable (Q : C ⥤ Arrow (Arrow C))
    (F : C ⥤ LoopPrespectrum.{w}) (c : ℕ)
    [∀ X n, T1Space ((F.obj X).space n)]
    (hF : ∀ X, HEP (F.obj X)) (hπF : ∀ X, Growth (F.obj X) c) (X : C) :
    IsStableEquivalence (strength Q F X) := by
  rw [strength_factor]
  let S := F.mapArrow.mapArrow.obj (Q.obj X)
  let : ∀ n, T1Space (S.left.left.space n) := fun n => inferInstanceAs
    (T1Space ((F.obj (Q.obj X).left.left).space n))
  let : ∀ n, T1Space (S.left.right.space n) := fun n => inferInstanceAs
    (T1Space ((F.obj (Q.obj X).left.right).space n))
  let : ∀ n, T1Space (S.right.left.space n) := fun n => inferInstanceAs
    (T1Space ((F.obj (Q.obj X).right.left).space n))
  let : ∀ n, T1Space (S.right.right.space n) := fun n => inferInstanceAs
    (T1Space ((F.obj (Q.obj X).right.right).space n))
  have hcone := coneStrength_stable S c
    (hF _) (hF _) (hF _) (hF _) (hπF _) (hπF _) (hπF _) (hπF _)
  apply (parameterLoopingMap_isStableEquivalence _ hcone).comp
  intro d
  exact ((stableHomotopyFunctor d).mapIso
    (LoopTranspose.iso (mappingCone (StrictSquare.comparison S)))).isIso_hom


end KTheory.Bass.LoopStable
