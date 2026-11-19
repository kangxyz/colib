/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusIntegralEtaleSignedPlacement
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusEtaleSignedPlacement

/-! # Native coefficient endpoints at signed weights

The endpoint comparison retains the native coefficient/extension isomorphism
and the native coefficient/shift isomorphism. This constructs endpoints only:
the parameter square connecting them remains a separate proof obligation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

/-- Forget integral coefficients on the original étale sheaves. -/
abbrev reducedTorusEtaleCoefficientFunctor :=
  sheafCompose (SmoothSite.etaleTopology (Spec (CommRingCat.of k)))
    (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat)

local instance : (reducedTorusEtaleCoefficientFunctor k).Additive where
  map_add := by intros; rfl

local notation "E" => Functor.mapHomologicalComplex
  (reducedTorusEtaleCoefficientFunctor k) (ComplexShape.up Int)

/-- The original extension comparison, with its actual cochain endpoints. -/
def reducedTorusEtaleCoefficientCochainIso (q : ℕ) :
    (E).obj (reducedTorusIntegralEtaleOrdinaryCochain k q) ≅
      reducedTorusEtaleOrdinaryCochain k q :=
  reducedTorusIntegralCoefficientExtendIso k q

/-- Forgetting coefficients at a signed weight keeps the native shift comparison. -/
def reducedTorusEtaleCoefficientSignedIso (q : ℕ) :
    (E).obj (reducedTorusIntegralEtaleOrdinarySigned k q) ≅
      reducedTorusEtaleOrdinarySigned k q :=
  ((E).commShiftIso (-(q : ℤ))).app (reducedTorusIntegralEtaleOrdinaryCochain k q) ≪≫
    (shiftFunctor _ (-(q : ℤ))).mapIso (reducedTorusEtaleCoefficientCochainIso k q)

/-- The signed endpoint has the explicit native shift and coefficient tail. -/
theorem reducedTorusEtaleCoefficientSignedIso_hom (q : ℕ) :
    (reducedTorusEtaleCoefficientSignedIso k q).hom =
      ((E).commShiftIso (-(q : ℤ))).hom.app
        (reducedTorusIntegralEtaleOrdinaryCochain k q) ≫
      (shiftFunctor _ (-(q : ℤ))).map (reducedTorusIntegralCoefficientExtendIso k q).hom :=
  rfl

end AlgebraicGeometry.PresheafWithTransfers
