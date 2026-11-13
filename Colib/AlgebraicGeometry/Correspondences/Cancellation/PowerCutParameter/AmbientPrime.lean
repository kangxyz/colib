/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCutParameter.AmbientGraph
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCutParameter.Prime

/-!
# Admissible prime image under the ambient parameter graph

The graph on the whole original product restricts to the exact finite graph
of a prime support. Its point image is therefore admissible for all large
exponents, with the same source component.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme SmoothSite

attribute [local instance] Stacks.Chow.isIntegral_integralComponentAt

variable (k : Type u) [Field k] (X Y : SmoothSite (Spec (.of k)))

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Gₘ" => multiplicativeGroupObject Sₖ
local notation "XG" => (product X Gₘ)
local notation "YG" => (product Y Gₘ)
local notation "V" => (torusPowerCutRetainedTarget k Y)

/-- The actual ambient power graph sends an admissible prime to an admissible
prime for every sufficiently large exponent. -/
theorem exists_isFiniteCorrespondencePoint_torusPowerParameterAmbientGraph
    (z : torusPowerCutAmbient k X Y) (hz : IsFiniteCorrespondencePoint (XG).hom (YG).hom z)
    (u₀ : (Γ((YG).left, ⊤))ˣ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      IsFiniteCorrespondencePoint (XG).hom (V).hom
        (torusPowerParameterAmbientGraph k (X := X) n u₀ z) := by
  let W := integralComponentAt (X := torusPowerCutAmbient k X Y) z
  let v := Units.map (torusPowerCutTarget k X Y z).appTop.hom.toMonoidHom u₀
  obtain ⟨N, hN⟩ := exists_isFiniteCorrespondencePoint_torusPowerCutRetainedPrimeMap
    k X Y z hz v
  refine ⟨N, fun n hn => ?_⟩
  let J := torusPowerParameterAmbientGraph k (X := X) n u₀
  have hcomp : W.subschemeι ≫ J = torusPowerCutRetainedPrimeMap k X Y z n v :=
    torusPowerParameterAmbientGraph_comp k n u₀ W.subschemeι
  have hpoint : torusPowerCutRetainedPrimeMap k X Y z n v (genericPoint W.subscheme) = J z := by
    rw [← hcomp]
    exact congrArg J (genericPointOf_integralComponentAt z)
  exact hpoint ▸ (hN n hn).2.2

end AlgebraicGeometry.Cor
