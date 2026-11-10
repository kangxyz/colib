/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.DVRConstantPrimeSeparable

noncomputable section

open Polynomial IsLocalRing Module
open scoped TensorProduct

universe u

open Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

variable (k R S F : Type u)
  [Field k]
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra k R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [IsLocalHom (algebraMap R S)]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Algebra k F] [IsScalarTower k R F]
  {d : ℕ} (p : MonicIrreducibleOfDegree k d)

local instance japaneseConstantCoverConsumer_nativeIrreducible : Fact (Irreducible (poly p)) :=
  ⟨irreducible p⟩

variable [Normal k (AdjoinRoot (poly p))]
  [Fact (Irreducible ((poly p).map (algebraMap k F)))]
  [Algebra S (AdjoinRoot ((poly p).map (algebraMap k F)))]
  [IsFractionRing S (AdjoinRoot ((poly p).map (algebraMap k F)))]
  [IsScalarTower R S (AdjoinRoot ((poly p).map (algebraMap k F)))]
  [Algebra.IsSeparable (ResidueField R) (ResidueField S)]

local instance japaneseConstantCoverConsumer_genericFinite :
    Module.Finite F (AdjoinRoot ((poly p).map (algebraMap k F))) :=
  ((monic p).map _).finite_adjoinRoot

example
    (hR : IsJapaneseRing R) (hsep : (poly p).Separable) (hp : d.Prime) (n : ℕ)
    (x : MilnorKTheory
      (AdjoinRoot ((poly p).map (algebraMap k F))) (n + 1)) :
    dvrMilnorTameSymbol' R F n
        (milnorKNorm F
          (AdjoinRoot ((poly p).map (algebraMap k F))) (n + 1) x) =
      milnorKNorm (ResidueField R)
        (ResidueField S) n
        (dvrMilnorTameSymbol'
          S
          (AdjoinRoot ((poly p).map (algebraMap k F))) n x) :=
  dvrMilnorTameSymbol'_milnorKNorm_of_japanese_separable_constant_cover
    k R S F p hR hsep hp n x

end
