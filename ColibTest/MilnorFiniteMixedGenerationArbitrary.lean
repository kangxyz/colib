module

import Colib.RingTheory.KTheory.MilnorK.FiniteMixedGenerationArbitrary

noncomputable section

open Polynomial IntermediateField Stacks.Chow

universe u

/-- The mixed witness uses the original native fields and literal coefficient
map, with no separability assumption on the base or its auxiliary extension. -/
example {k : Type u} [Field k] (p : k[X]) (hp : p.Monic)
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
                (p.map (algebraMap k S)) dvd_rfl) (m + 1) x :=
  exists_finite_coprime_milnorK_mixed_expansion_arbitrary p hp hprime m x

end
