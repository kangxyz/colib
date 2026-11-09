module

import Colib.RingTheory.AdjoinRoot.FactorIndexEquiv

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

variable {k : Type*} [Field k]

-- The native subtype is finite and the complete factor correspondence is bijective.
example (f : k[X]) (hf : f ≠ 0) :
    Finite {q : Σ d : ℕ, MonicIrreducibleOfDegree k d // poly q.2 ∣ f} ∧
      Function.Bijective (AdjoinRoot.maximalFactorIndexEquiv f hf) :=
  ⟨AdjoinRoot.finite_nativeFactorIndex f hf,
    (AdjoinRoot.maximalFactorIndexEquiv f hf).bijective⟩

-- This is equality of the original maximal ideal, not only its polynomial pullback.
example (f : k[X]) (hf : f ≠ 0) (m : MaximalSpectrum (AdjoinRoot f)) :
    m.asIdeal = RingHom.ker (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr
        (AdjoinRoot.maximalFactorIndexEquiv f hf m).2)) :=
  AdjoinRoot.maximalFactorIndexEquiv_asIdeal f hf m

-- The selected point's actual quotient comparison retains every whole-algebra element.
example (f : k[X]) (hf : f ≠ 0) (m : MaximalSpectrum (AdjoinRoot f))
    (x : AdjoinRoot f) :
    AdjoinRoot.maximalFactorQuotientEquiv f hf m (Ideal.Quotient.mk m.asIdeal x) =
      Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
        (AdjoinRoot.maximalFactorIndexEquiv f hf m).2) x :=
  AdjoinRoot.maximalFactorQuotientEquiv_mk f hf m x

variable (p h : k[X]) [Fact (Irreducible p)] [Fact (Irreducible h)]

-- Tensor swap matches the literal kernels on both complete native factor indices.
example
    (q : {q : Σ d : ℕ, MonicIrreducibleOfDegree (AdjoinRoot p) d //
      poly q.2 ∣ h.map (algebraMap k (AdjoinRoot p))}) :
    RingHom.ker (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
        (AdjoinRoot.tensorSwapFactorIndexEquiv p h q).2)) =
      (RingHom.ker (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr q.2))).map
          (AdjoinRoot.tensorSwapEquiv p h).toRingHom :=
  AdjoinRoot.tensorSwapFactorIndexEquiv_ker p h q

-- The quotient square uses the same bijection, not an independently chosen branch.
example
    (q : {q : Σ d : ℕ, MonicIrreducibleOfDegree (AdjoinRoot p) d //
      poly q.2 ∣ h.map (algebraMap k (AdjoinRoot p))})
    (x : AdjoinRoot (h.map (algebraMap k (AdjoinRoot p)))) :
    AdjoinRoot.tensorSwapFactorQuotientEquiv p h q
        (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr q.2) x) =
      Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
        (AdjoinRoot.tensorSwapFactorIndexEquiv p h q).2)
          (AdjoinRoot.tensorSwapEquiv p h x) :=
  AdjoinRoot.tensorSwapFactorQuotientEquiv_factor p h q x
