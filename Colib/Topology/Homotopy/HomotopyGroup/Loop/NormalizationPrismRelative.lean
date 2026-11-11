/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.Loop.NormalizationPrismNaturality

/-!
# Relative parameterized normalization

The whole prism fixes every input on which the original component, self-track, and specified
null are constant. This includes the chosen basepoint and any additional prescribed zero face.
The proof uses the complete pointwise dependence theorem, not a homotopy-group computation.
-/
@[expose] public section
noncomputable section
open scoped Topology unitInterval
universe u v
namespace Topology.LoopNormalizationPrism
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {y : Y}
variable (γ : C(X, Path y y)) (α : γ.Homotopy γ)
  (N : γ.Homotopy (ContinuousMap.const X (Path.refl y)))

/-- A point at which all three inputs are constant is fixed throughout the full prism. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrismRelative.lean:27"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
theorem normalizationHomotopy_fixed (x : X) (hγ : γ x = Path.refl y)
    (hα : ∀ t, α (t, x) = Path.refl y) (hN : ∀ t, N (t, x) = Path.refl y)
    (r : unitInterval) :
    normalizationHomotopy γ α N (r, x) = Path.refl (Path.refl y) := by
  let γ₀ : C(Unit, Path () ()) := ContinuousMap.const Unit (Path.refl ())
  let H₀ := ContinuousMap.Homotopy.refl γ₀
  apply Path.ext
  funext t
  apply Path.ext
  funext s
  exact normalizationHomotopy_pointwise id (fun _ : Unit ↦ y)
    γ α N γ₀ H₀ H₀ x ()
    (fun z ↦ congrArg (fun p : Path y y ↦ p z) hγ)
    (fun u z ↦ congrArg (fun p : Path y y ↦ p z) (hα u))
    (fun u z ↦ congrArg (fun p : Path y y ↦ p z) (hN u)) r t s

/-- The normalization prism relative to any set of genuine constant input faces. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyGroups/Loop/NormalizationPrismRelative.lean:44"
  "adaptation" "Original moving-prefix normalization with independent clocks and whole null"]
def normalizationHomotopyRel (S : Set X)
    (hγ : ∀ x ∈ S, γ x = Path.refl y)
    (hα : ∀ t x, x ∈ S → α (t, x) = Path.refl y)
    (hN : ∀ t x, x ∈ S → N (t, x) = Path.refl y) :
    (normalized γ α).HomotopyRel (nullConjugate γ α N) S where
  toHomotopy := normalizationHomotopy γ α N
  prop' r x hx :=
    (normalizationHomotopy_fixed γ α N x (hγ x hx)
      (fun t ↦ hα t x hx) (fun t ↦ hN t x hx) r).trans
        ((normalizationHomotopy_fixed γ α N x (hγ x hx)
          (fun t ↦ hα t x hx) (fun t ↦ hN t x hx) 0).symm.trans
            ((normalizationHomotopy γ α N).apply_zero x))

end Topology.LoopNormalizationPrism

attribute [colib_tag "COL-0552"]
  Topology.LoopNormalizationPrism.normalizationHomotopyRel
