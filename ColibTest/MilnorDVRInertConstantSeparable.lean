/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.DVRInertConstantSeparable

noncomputable section

open Polynomial IsLocalRing Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

universe u

attribute [local instance] Ideal.Quotient.field

attribute [local instance]
  Stacks.Chow.inertConstant_nativeIrreducible
  Stacks.Chow.inertConstant_isDomain
  Stacks.Chow.inertConstant_isLocalRing
  Stacks.Chow.inertConstant_isDiscreteValuationRing
  Stacks.Chow.inertConstant_finite
  Stacks.Chow.inertConstant_torsionFree
  Stacks.Chow.inertConstant_isLocalHom
  Stacks.Chow.inertConstant_fractionAlgebra
  Stacks.Chow.inertConstant_fractionTower
  Stacks.Chow.inertConstant_isFractionRing
  Stacks.Chow.inertConstant_finiteGeneric

variable (k R F : Type u) [Field k]
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra k R]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Algebra k F] [IsScalarTower k R F]
  {d : ℕ} (p : MonicIrreducibleOfDegree k d)
  [hred : Fact (Irreducible (((poly p).map (algebraMap k R)).map (residue R)))]

local notation "S" => AdjoinRoot (Polynomial.map (algebraMap k R) (poly p))
local notation "E" => AdjoinRoot (Polynomial.map (algebraMap k F) (poly p))

variable [Normal k (AdjoinRoot (poly p))]

example
    (hR : IsJapaneseRing R) (hsep : (poly p).Separable) (hp : d.Prime) :
    letI : Fact (Irreducible ((poly p).map (algebraMap k F))) :=
      inertConstant_genericIrreducible k R F p
    ∀ (n : ℕ) (x : MilnorKTheory E (n + 1)),
      dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) =
        milnorKNorm (ResidueField R) (ResidueField S) n
          (dvrMilnorTameSymbol' S E n x) := by
  let : Fact (Irreducible ((poly p).map (algebraMap k F))) :=
    inertConstant_genericIrreducible k R F p
  intro n x
  exact dvrMilnorTameSymbol'_milnorKNorm_inert_constant_of_separable
    k R F p hR hsep hp n x

end
