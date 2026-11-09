/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.FiniteMixedWitnesses
public import Colib.FieldTheory.Polynomial.CoprimeDegree
public import Colib.FieldTheory.FiniteCoprimeSplittingArbitrary

/-!
# Finite coprime mixed generation over an arbitrary field

This retains the original reduced representatives, literal coefficient image,
native root fields and native coefficient-factor map. The finite auxiliary
coefficient extension need not be separable. This is exactly the scope needed by
the coprime-annihilator argument in normal-prime presentation independence.
-/

@[expose] public noncomputable section

namespace Stacks.Chow

open Polynomial IntermediateField

universe u

variable {k : Type u} [Field k]

/-- Every class of positive degree in a prime-degree root field has a finite
signed mixed expansion after a finite prime-to-degree coefficient extension.
Neither the base nor the auxiliary extension is assumed perfect or separable. -/
theorem exists_finite_coprime_milnorK_mixed_expansion_arbitrary
    (p : k[X]) (hp : p.Monic)
    [Fact (Irreducible p)] (hprime : p.natDegree.Prime) (m : ℕ)
    (x : MilnorKTheory (AdjoinRoot p) (m + 1)) :
    ∃ s : Finset k[X],
      (∀ r ∈ s, r ≠ 0 ∧ r.natDegree < p.natDegree) ∧
      ∃ S : IntermediateField k (∏ r ∈ s, r).SplittingField,
        FiniteDimensional k S ∧
        p.natDegree.Coprime (Module.finrank k S) ∧
        (∀ r ∈ s, (r.map (algebraMap k S)).Splits) ∧
        ∃ hq : Irreducible (p.map (algebraMap k S)),
          let _ : Fact (Irreducible (p.map (algebraMap k S))) := ⟨hq⟩
          ∃ c : ((Fin m → Sˣ) × (AdjoinRoot (p.map (algebraMap k S)))ˣ) →₀ ℤ,
            (c.sum fun ab z => z • milnorKTupleSymbol
              (Fin.snoc (Units.map
                (algebraMap S (AdjoinRoot (p.map (algebraMap k S)))).toMonoidHom ∘ ab.1)
                ab.2)) =
              milnorKTheoryMap (AdjoinRoot.map (algebraMap k S) p
                (p.map (algebraMap k S)) dvd_rfl) (m + 1) x := by
  refine (exists_finite_milnorK_reduced_mixed_expansion.{u, u} p hp m x).elim ?_
  intro s hsgen
  have hs := hsgen.1
  have hgen := hsgen.2
  let : Fact p.natDegree.Prime := ⟨hprime⟩
  refine (exists_coprime_splitting_field_of_finset_arbitrary p.natDegree s
    (fun r hr => (hs r hr).1) (fun r hr => (hs r hr).2)).elim ?_
  intro S hS
  have hfinite := hS.1
  have hcop := hS.2.1
  have hsplit := hS.2.2
  let : FiniteDimensional k S := hfinite
  have hq : Irreducible (p.map (algebraMap k S)) :=
    hp.irreducible_map_of_natDegree_coprime (Fact.out : Irreducible p) hcop
  let : Fact (Irreducible (p.map (algebraMap k S))) := ⟨hq⟩
  refine ⟨s, hs, S, hfinite, hcop, hsplit, hq, ?_⟩
  dsimp only
  exact hgen S (algebraMap k S) (p.map (algebraMap k S)) dvd_rfl hsplit

end Stacks.Chow
