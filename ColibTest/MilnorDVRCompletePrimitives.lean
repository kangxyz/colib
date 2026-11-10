/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.AdjoinRoot.TensorScalarFactors
import Colib.RingTheory.KTheory.MilnorK.Norm.DVRRestrictionKernel

/-! Full-statement consumers of the two lower complete-DVR assembly primitives. -/

noncomputable section

open Stacks.Chow Polynomial Stacks.Chow.MonicIrreducibleOfDegree AdjoinRoot IsLocalRing
open scoped TensorProduct

universe u v

example {k : Type u} [Field k] {L : Type v} [Field L] [Algebra k L]
    {d : ℕ} (p : MonicIrreducibleOfDegree k d) (hs : (poly p).Separable)
    (a : AdjoinRoot (poly p))
    (r : {r : Σ e : ℕ, MonicIrreducibleOfDegree L e //
      poly r.2 ∣ (poly p).map (algebraMap k L)}) :
    tensorScalarFactorsEquiv p hs (1 ⊗ₜ[k] a) r =
      AdjoinRoot.map (algebraMap k L) (poly p) (poly r.1.2) r.2 a := by
  exact tensorScalarFactorsEquiv_tmul_one p hs a r

example
    (R S F E : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    [IsLocalHom (algebraMap R S)]
    [Field F] [Algebra R F] [IsFractionRing R F]
    [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
    [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (n : ℕ) (z : MilnorKTheory (ResidueField R) n)
    (hz : e • milnorKTheoryMap (algebraMap (ResidueField R) (ResidueField S)) n z = 0) :
    Module.finrank F E • z = 0 := by
  exact finrank_smul_eq_zero_of_ramified_residue_restrict R S F E hπ hϖ u e he n z hz

end
