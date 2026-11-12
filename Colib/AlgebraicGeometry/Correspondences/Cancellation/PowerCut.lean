/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.GroupScheme.LaurentOpen
public import Colib.AlgebraicGeometry.Sites.Smooth.GroupSchemes
public import Colib.AlgebraicGeometry.Sites.Smooth.Products

/-!
# The two torus power-cut equations

Pull the forward unit back along a torus projection. The numerator and
denominator are the literal power-cut equations on those units.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Gₘ" => SmoothSite.multiplicativeGroupObject Sₖ

/-- The native forward torus coordinate on the original support. -/
def torusSupportCoordinate {X : SmoothSite Sₖ} {P : Scheme.{u}}
    (p : P ⟶ (SmoothSite.product X Gₘ).left) : (Γ(P, ⊤))ˣ :=
  Units.map (p ≫ (SmoothSite.productSnd X Gₘ).left).appTop.hom.toMonoidHom
    (multiplicativeGroupBaseChangeCoordinate Sₖ)

/-- The base projection of the original torus support. -/
abbrev torusSupportBaseProjection {X : SmoothSite Sₖ} {P : Scheme.{u}}
    (p : P ⟶ (SmoothSite.product X Gₘ).left) : P ⟶ X.left :=
  p ≫ (SmoothSite.productFst X Gₘ).left

/-- The numerator of Voevodsky's power cut at the source unit. -/
def torusPowerCutNumerator {R : Type u} [CommRing R] (t : Rˣ) (n : ℕ) : R :=
  (t : R) ^ (n + 1) - 1

/-- The denominator compares the source power with the target unit. -/
def torusPowerCutDenominator {R : Type u} [CommRing R] (t u₀ : Rˣ) (n : ℕ) : R :=
  (t : R) ^ (n + 1) - (u₀ : R)

end AlgebraicGeometry.Cor
