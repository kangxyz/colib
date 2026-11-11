/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.FiniteConeStrength
public import Colib.KTheory.Bass.IteratedLoopStrength
public import Colib.Topology.Prespectrum.LoopTranspose

/-!
# The fixed-order finite iteration of the original loop strength

The original strength components give an actual natural transformation. Its iteration uses
`kappa_(Omega^j G)` first and then `Omega(kappa^j_G)`, without changing the original transpose
or choosing another comparison. For genuine finite normalized Model stages each component
is stable by the already proved single-strength result and stability under parameter looping.
-/
@[expose] public section
noncomputable section
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open CategoryTheory Topology Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open Topology.LoopPrespectrum.FiniteParameterLooping
universe u v w
namespace KTheory.Bass.IteratedLoopStrength
open LoopStrength FiniteConeTopology FiniteConeStrength
variable {C : Type u} [Category.{v} C]

/-- Each prescribed finite iterated strength is stable on every unlooped Model cone stage. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/IteratedLoopStrength.lean:55"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem iterated_model_stable (Q : C ⥤ Arrow (Arrow C)) (i j : ℕ)
    (M : C ⥤ WideSubcategory preservesZero.{w}) (X : C) :
    IsStableEquivalence
      ((iteratedStrength Q j (iterate Q i (M ⋙ prespectrumFunctor))).app X) := by
  induction j with
  | zero =>
    intro d
    change IsIso ((stableHomotopyFunctor d).map (𝟙 _))
    infer_instance
  | succ j ih =>
    exact (model_strength_stable Q i j M X).comp
      (parameterLoopingMap_isStableEquivalence _ ih)

end KTheory.Bass.IteratedLoopStrength
