/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Covering.PullbackSimplyConnected
public import Colib.Topology.LocalCoefficients.PullbackCoveringHomology
public import Colib.Topology.PlusConstruction.DisplayedComparisonChains

/-!
# The actual simply connected pullback of a displayed plus comparison

Given a simply connected covering of the target and an actual comparison under
the original source, the literal pullback is simply connected and its second
projection induces a quasi-isomorphism on integral singular chains. These are
the inputs for a subsequent homological Whitehead argument, not a substitute
for that argument or for constructing the comparison.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory FundamentalGroupoid
open scoped Topology

namespace Topology.IsPlusConstruction

variable {X Y Z E : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] [TopologicalSpace E]
  [PathConnectedSpace Y] [SimplyConnectedSpace E]

omit [PathConnectedSpace Y] [SimplyConnectedSpace E] in
private theorem piOne_bijective_iff_at_endpoint (k : C(Y, Z)) {y : Y} {z : Z}
    (h : k y = z) :
    Function.Bijective (HomotopyGroup.piMap 0 k h) ↔
      Function.Bijective (HomotopyGroup.piMap 0 k (x := y) rfl) := by
  cases h
  rfl

/-- The projection of the actual pullback preserves integral homology, and its
source is simply connected; the coherence path to the chosen pair is retained. -/
theorem displayedComparison_simplyConnected_pullback_singular_quasiIso
    (f : C(X, Y)) (g : C(X, Z)) (k : C(Y, Z)) (H : (k.comp f).Homotopy g)
    {x : X} {y : Y} {z : Z} (γ : Path (f x) y) (δ : Path (g x) z)
    (N : Subgroup (HomotopyGroup.Pi 1 X x))
    (hf : IsPlusConstruction.{u, u, u} f γ N)
    (hg : IsPlusConstruction.{u, u, u} g δ N)
    (q : C(E, Z)) (hq : IsCoveringMap q) (e : E) (he : k y = q e) :
    SimplyConnectedSpace (Covering.Pullback.Space k q) ∧
      QuasiIso (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj
        LocalCoefficients.integralCoefficients).map
          (TopCat.ofHom (Covering.Pullback.lift k q))) := by
  have h₁ := displayedComparison_piOne_bijective f g k H γ δ N hf hg
  have h₁' := (piOne_bijective_iff_at_endpoint k he).mpr h₁
  exact ⟨Covering.Pullback.simplyConnectedSpace k q hq ⟨(y, e), he⟩ h₁',
    LocalCoefficients.PullbackCovering.pullback_singular_quasiIso_of_all_localCoefficients
      hq k (fun A ↦ displayedComparison_twisted_quasiIso f g k H γ δ N hf hg A)⟩

end Topology.IsPlusConstruction
