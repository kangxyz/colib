/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.CoherentClosedPushforward
public import Colib.RingTheory.KTheory.GTheory.FiniteModules.PrincipalClosedLocalization

/-!
# The actual principal closed pushforward under affine G-comparison

This specializes the geometric direct-image square to the principal quotient.
The target map is precisely the existing finite-module closed pushforward used
in principal dévissage and its localization sequence.

Implementation source: `Quillen/AlgebraicGeometry/Scheme/PrincipalClosedGTheory.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd` (the original closed pushforward).
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.ExactCategory
namespace AlgebraicGeometry.Scheme.Modules.Coherent
variable (R : CommRingCat.{u}) [IsNoetherianRing R] (f : R)

/-- The original principal closed G-map is the actual quotient scalar restriction. -/
theorem publicSpecGRingEquiv_principalClosedPushforward (n : ℕ) :
    (publicSpecGRingEquiv R n).toMonoidHom.comp
      (Scheme.closedPushforwardG
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))) n) =
    (FGModuleCat.Localization.closedPushforwardKMap.{u, u} f n).comp
      (publicSpecGRingEquiv (CommRingCat.of (FGModuleCat.ClosedRing f)) n).toMonoidHom := by
  exact publicSpecGRingEquiv_closedPushforward
    (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))
    (RingHom.Finite.of_surjective _ (Ideal.Quotient.mk_surjective)) n

end AlgebraicGeometry.Scheme.Modules.Coherent
