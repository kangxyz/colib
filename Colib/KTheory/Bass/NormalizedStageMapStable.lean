/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.IteratedLoopStrengthStable
public import Colib.KTheory.Bass.NormalizedStageMap
public import Colib.Topology.Prespectrum.LoopTranspose
public import Colib.KTheory.Bass.StrictDiagramStableEquivalence

/-!
# Actual finite stage maps into loop-normalized cone iterates

The map from the original finite Bass stage to `Omega^i C^i F` is formed from the original
Bass image of the preceding map and the fixed-order iterated loop strength. Both full functor
identifications are retained as explicit equality transports. Genuine Model input makes each
stage map stable through existing Bass stable preservation and the proved topology of both
actual finite stages. These are stage maps only: no compatibility with successive seed
transitions, no equality of geometric chi with cone-loop strength, and no tower comparison
is asserted.
-/
@[expose] public section
noncomputable section
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open CategoryTheory Topology Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open Topology.LoopPrespectrum.FiniteParameterLooping
universe u v w
namespace KTheory.Bass.NormalizedStageMap
open FiniteConeTopology FiniteConeStrength IteratedLoopStrength
variable {C : Type u} [Category.{v} C]

private theorem eqToHom_app_stable {F G : C ⥤ LoopPrespectrum.{w}} (h : F = G) (X : C) :
    IsStableEquivalence ((eqToHom h).app X) := by
  subst G
  intro d
  change IsIso ((stableHomotopyFunctor d).map (𝟙 _))
  infer_instance

/-- Every actual stage map is stable for genuine Model input, without later-stage assumptions. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/NormalizedStageMap.lean:81"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem model_stageMap_stable (Q : C ⥤ Arrow (Arrow C)) (i : ℕ)
    (M : C ⥤ WideSubcategory preservesZero.{w}) (X : C) :
    IsStableEquivalence ((stageMap Q i (M ⋙ prespectrumFunctor)).app X) := by
  induction i generalizing X with
  | zero =>
    intro d
    change IsIso ((stableHomotopyFunctor d).map (𝟙 _))
    infer_instance
  | succ i ih =>
    have hR : ∀ Y n, TopCat.HomotopyExtensionProperty
        (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1}
          (((normalized Q i (M ⋙ prespectrumFunctor)).obj Y).point n))) := by
      intro Y n
      rw [normalized_obj]
      exact modelLoopsIterate_point_homotopyExtensionProperty Q i i M Y n
    have hπR : ∀ Y n k, k < n + 2 →
        ∀ x : ((normalized Q i (M ⋙ prespectrumFunctor)).obj Y).space (n + i + 2),
          Subsingleton (HomotopyGroup.Pi k
            (((normalized Q i (M ⋙ prespectrumFunctor)).obj Y).space (n + i + 2)) x) := by
      intro Y n k hk
      rw [normalized_obj]
      exact modelLoopsIterate_homotopyGroup_subsingleton Q i i M Y n k hk
    have hB := strictDiagramFunctor_map_isStableEquivalence_of_linearGrowth Q
      ((strictDiagramIterate Q i).obj (M ⋙ prespectrumFunctor))
      (normalized Q i (M ⋙ prespectrumFunctor))
      (modelDiagramIterate_point_homotopyExtensionProperty Q i M) hR i i
      (fun Y n k hk x => modelDiagramIterate_homotopyGroup_subsingleton_at
        Q i M Y n k hk x) hπR (stageMap Q i (M ⋙ prespectrumFunctor)) ih X
    exact (eqToHom_app_stable (bass_succ_eq Q i (M ⋙ prespectrumFunctor)) X).comp
      (hB.comp ((iterated_model_stable Q i i M X).comp
        (eqToHom_app_stable (normalized_succ_eq Q i (M ⋙ prespectrumFunctor)) X)))

end KTheory.Bass.NormalizedStageMap

namespace KTheory.Bass.NormalizedStageMap

attribute [colib_tag "COL-0565"] model_stageMap_stable

end KTheory.Bass.NormalizedStageMap
