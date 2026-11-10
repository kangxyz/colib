module

import Colib.RingTheory.KTheory.MilnorK.Norm.RationalFactorIndex

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree
open scoped BigOperators

variable {k : Type*} [Field k]

local instance milnorRationalFactorIndexDecidableEq (K : Type*) [Field K] :
    DecidableEq (Σ d : ℕ, MonicIrreducibleOfDegree K d) :=
  Classical.decEq _

-- Every rational factor is attained, without any assumed factor coverage.
example (f : k[X]) (hf : f.Monic)
    (q : Σ d : ℕ, MonicIrreducibleOfDegree (RatFunc k) d)
    (hq : poly q.2 ∣ f.map (RatFunc.C : k →+* RatFunc k)) :
    ∃ p : Σ d : ℕ, MonicIrreducibleOfDegree k d,
      poly p.2 ∣ f ∧
        (⟨p.1, p.2.ratFunc⟩ : Σ d : ℕ, MonicIrreducibleOfDegree (RatFunc k) d) = q :=
  exists_ratFunc_of_dvd_map f hf q hq

-- The equivalence keeps the actual degree and polynomial, and its inverse is genuine.
example (f : k[X]) (hf : f.Monic)
    (p : {p : Σ d : ℕ, MonicIrreducibleOfDegree k d // poly p.2 ∣ f}) :
    (ratFuncFactorIndexEquiv f hf p).1.1 = p.1.1 ∧
      poly (ratFuncFactorIndexEquiv f hf p).1.2 = (poly p.1.2).map RatFunc.C ∧
      (ratFuncFactorIndexEquiv f hf).symm (ratFuncFactorIndexEquiv f hf p) = p :=
  ⟨ratFuncFactorIndexEquiv_degree f hf p, ratFuncFactorIndexEquiv_poly f hf p,
    (ratFuncFactorIndexEquiv f hf).symm_apply_apply p⟩

-- Finiteness and complete image coverage are conclusions, in arbitrary characteristic.
example (f : k[X]) (hf : f.Monic) :
    Finite {p : Σ d : ℕ, MonicIrreducibleOfDegree k d // poly p.2 ∣ f} ∧
      Finite {q : Σ d : ℕ, MonicIrreducibleOfDegree (RatFunc k) d //
        poly q.2 ∣ f.map (RatFunc.C : k →+* RatFunc k)} ∧
      ∃ S : Finset (Σ d : ℕ, MonicIrreducibleOfDegree k d),
        (∀ p, p ∈ S ↔ poly p.2 ∣ f) ∧
        ∀ q : Σ d : ℕ, MonicIrreducibleOfDegree (RatFunc k) d,
          q ∈ S.image (fun p =>
            (⟨p.1, p.2.ratFunc⟩ : Σ d : ℕ, MonicIrreducibleOfDegree (RatFunc k) d)) ↔
            poly q.2 ∣ f.map (RatFunc.C : k →+* RatFunc k) :=
  ⟨(finite_ratFuncFactorIndices f hf).1, (finite_ratFuncFactorIndices f hf).2,
    exists_finset_image_ratFunc f hf⟩

-- An arbitrary rational factor is the literal constant image of its inverse polynomial.
example (f : k[X]) (hf : f.Monic)
    (q : {q : Σ d : ℕ, MonicIrreducibleOfDegree (RatFunc k) d //
      poly q.2 ∣ f.map (RatFunc.C : k →+* RatFunc k)}) :
    ((ratFuncFactorIndexEquiv f hf).symm q).1.1 = q.1.1 ∧
      (poly ((ratFuncFactorIndexEquiv f hf).symm q).1.2).map RatFunc.C = poly q.1.2 :=
  ⟨ratFuncFactorIndexEquiv_symm_degree f hf q, ratFuncFactorIndexEquiv_symm_poly f hf q⟩

-- The full dependent-index sum transports its actual integer multiplicity weights.
example {M : Type*} [AddCommGroup M] (f : k[X]) (hf : f.Monic)
    [Fintype {p : Σ d : ℕ, MonicIrreducibleOfDegree k d // poly p.2 ∣ f}]
    [Fintype {q : Σ d : ℕ, MonicIrreducibleOfDegree (RatFunc k) d //
      poly q.2 ∣ f.map (RatFunc.C : k →+* RatFunc k)}]
    (F : {q : Σ d : ℕ, MonicIrreducibleOfDegree (RatFunc k) d //
      poly q.2 ∣ f.map (RatFunc.C : k →+* RatFunc k)} → M) :
    ∑ q : {q : Σ d : ℕ, MonicIrreducibleOfDegree (RatFunc k) d //
        poly q.2 ∣ f.map (RatFunc.C : k →+* RatFunc k)},
        (multiplicity (poly q.1.2) (f.map RatFunc.C) : ℤ) • F q =
      ∑ p : {p : Σ d : ℕ, MonicIrreducibleOfDegree k d // poly p.2 ∣ f},
        (multiplicity (poly p.1.2) f : ℤ) • F (ratFuncFactorIndexEquiv f hf p) := by
  rw [sum_ratFuncFactorIndexEquiv f hf]
  apply Finset.sum_congr rfl
  intro p _
  change (multiplicity (poly p.1.2.ratFunc) (f.map RatFunc.C) : ℤ) • _ = _
  rw [multiplicity_ratFunc]
