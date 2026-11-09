/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdjoinRoot.MaximalFactors
public import Colib.RingTheory.AdjoinRoot.TensorSwap
public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.PolyResidueRing

/-!
# The native finite factor index and the actual maximal spectrum

For a nonzero polynomial, its actual maximal spectrum is equivalent to the subtype
of the existing sigma of native monic irreducible points cut out by divisibility.
The reverse map is the kernel of the literal quotient factor map. The associated
quotient equivalence retains that map on every element of the whole algebra.

Composing these equivalences with the existing tensor swap gives a bijection of
the complete factor indices, together with their actual quotient equivalences.
Repeated factors remain in the whole algebra; this index counts distinct points.
No new point, branch, field, norm, or residue model is introduced. In particular,
the quotient comparisons here do not assert compatibility of any chosen norms.

The maximal-ideal argument uses `MaximalFactors`, whose source comparison is with
`Aglib/RingTheory/AdjoinRootScalarBranches.lean` at revision
`52e09db47998f139064acf48a2d3a64494d0dd9a`. The dependent-index extensionality argument
is the same native argument as `MonicIrreducibleOfDegree.sigma_poly_injective` in
`Norm/CoefficientFactorSupport`, without importing that higher application layer.
-/

@[expose] public noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

namespace AdjoinRoot

variable {k : Type*} [Field k]

private theorem factorIndexEquiv_sigma_poly_injective :
    Function.Injective (fun q : Σ d : ℕ, MonicIrreducibleOfDegree k d => poly q.2) := by
  intro q r h
  obtain ⟨d, q⟩ := q
  obtain ⟨e, r⟩ := r
  change poly q = poly r at h
  obtain rfl : d = e := by rw [← natDegree_eq q, h, natDegree_eq r]
  obtain rfl := poly_injective h
  rfl

/-- A native polynomial factor determines the actual kernel of its quotient map. -/
def nativeFactorMaximal (f : k[X])
    (q : {q : Σ d : ℕ, MonicIrreducibleOfDegree k d // poly q.2 ∣ f}) :
    MaximalSpectrum (AdjoinRoot f) := by
  letI factorIndexEquivIrreducible : Fact (Irreducible (poly q.1.2)) :=
    ⟨irreducible q.1.2⟩
  let F : AdjoinRoot f →+* AdjoinRoot (poly q.1.2) :=
    Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr q.2)
  exact ⟨RingHom.ker F,
    RingHom.ker_isMaximal_of_surjective F (Ideal.Quotient.factor_surjective _)⟩

/-- Pulling the actual maximal ideal back gives the literal polynomial factor. -/
theorem nativeFactorMaximal_comap_mk (f : k[X])
    (q : {q : Σ d : ℕ, MonicIrreducibleOfDegree k d // poly q.2 ∣ f}) :
    (nativeFactorMaximal f q).asIdeal.comap (mk f) = Ideal.span {poly q.1.2} :=
  ker_factor_comap_mk f (poly q.1.2) q.2

/-- Distinct native monic factors give distinct actual maximal ideals. -/
theorem nativeFactorMaximal_injective (f : k[X]) :
    Function.Injective (nativeFactorMaximal f) := by
  intro q r h
  apply Subtype.ext
  apply factorIndexEquiv_sigma_poly_injective
  apply Polynomial.eq_of_monic_of_associated (monic q.1.2) (monic r.1.2)
  apply Ideal.span_singleton_eq_span_singleton.mp
  rw [← nativeFactorMaximal_comap_mk f q, ← nativeFactorMaximal_comap_mk f r, h]

/-- All actual maximal ideals are attained, with no factor enumeration supplied. -/
theorem nativeFactorMaximal_surjective (f : k[X]) (hf : f ≠ 0) :
    Function.Surjective (nativeFactorMaximal f) := by
  intro m
  obtain ⟨q, ⟨hqm, hqi, hqf, hq⟩, _⟩ :=
    existsUnique_monic_irreducible_factor_comap f hf m
  refine ⟨⟨⟨q.natDegree, ⟨q, hqm, hqi, rfl⟩⟩, hqf⟩, ?_⟩
  apply MaximalSpectrum.ext
  apply Ideal.comap_injective_of_surjective (mk f) mk_surjective
  exact (ker_factor_comap_mk f q hqf).trans hq

/-- The actual maximal spectrum is the existing native factor index. -/
def maximalFactorIndexEquiv (f : k[X]) (hf : f ≠ 0) :
    MaximalSpectrum (AdjoinRoot f) ≃
      {q : Σ d : ℕ, MonicIrreducibleOfDegree k d // poly q.2 ∣ f} :=
  (Equiv.ofBijective (nativeFactorMaximal f)
    ⟨nativeFactorMaximal_injective f, nativeFactorMaximal_surjective f hf⟩).symm

/-- The inverse equivalence is exactly the actual factor-map kernel. -/
theorem maximalFactorIndexEquiv_symm_asIdeal (f : k[X]) (hf : f ≠ 0)
    (q : {q : Σ d : ℕ, MonicIrreducibleOfDegree k d // poly q.2 ∣ f}) :
    ((maximalFactorIndexEquiv f hf).symm q).asIdeal =
      RingHom.ker (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr q.2)) :=
  rfl

/-- The selected native point cuts out the original maximal ideal itself. -/
theorem maximalFactorIndexEquiv_asIdeal (f : k[X]) (hf : f ≠ 0)
    (m : MaximalSpectrum (AdjoinRoot f)) :
    m.asIdeal = RingHom.ker (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (maximalFactorIndexEquiv f hf m).2)) :=
  (congrArg MaximalSpectrum.asIdeal
    ((maximalFactorIndexEquiv f hf).symm_apply_apply m)).symm

/-- The native divisibility subtype is finite, including for nonreduced quotients. -/
theorem finite_nativeFactorIndex (f : k[X]) (hf : f ≠ 0) :
    Finite {q : Σ d : ℕ, MonicIrreducibleOfDegree k d // poly q.2 ∣ f} := by
  classical
  let T : Set (Σ d : ℕ, MonicIrreducibleOfDegree k d) :=
    (fun q => poly q.2) ⁻¹' ((UniqueFactorizationMonoid.normalizedFactors f).toFinset :
      Set k[X])
  have hT : T.Finite :=
    (UniqueFactorizationMonoid.normalizedFactors f).toFinset.finite_toSet.preimage
      (fun _ _ _ _ h => factorIndexEquiv_sigma_poly_injective h)
  have hS : Set.Finite {q : Σ d : ℕ, MonicIrreducibleOfDegree k d | poly q.2 ∣ f} := by
    apply hT.subset
    intro q hq
    change poly q.2 ∈ (UniqueFactorizationMonoid.normalizedFactors f).toFinset
    exact Multiset.mem_toFinset.mpr
      ((Polynomial.mem_normalizedFactors_iff hf).mpr ⟨irreducible q.2, monic q.2, hq⟩)
  exact Set.finite_coe_iff.mpr hS

/-- The exact quotient at the selected native factor, using the original kernel. -/
def maximalFactorQuotientEquiv (f : k[X]) (hf : f ≠ 0)
    (m : MaximalSpectrum (AdjoinRoot f)) :
    (AdjoinRoot f ⧸ m.asIdeal) ≃+*
      AdjoinRoot (poly (maximalFactorIndexEquiv f hf m).1.2) := by
  let F : AdjoinRoot f →+* AdjoinRoot (poly (maximalFactorIndexEquiv f hf m).1.2) :=
    Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
      (maximalFactorIndexEquiv f hf m).2)
  have hker : m.asIdeal = RingHom.ker F := maximalFactorIndexEquiv_asIdeal f hf m
  exact (Ideal.quotEquivOfEq hker).trans
    (F.quotientKerEquivOfSurjective (Ideal.Quotient.factor_surjective _))

/-- On every element the quotient comparison is the literal native factor map. -/
theorem maximalFactorQuotientEquiv_mk (f : k[X]) (hf : f ≠ 0)
    (m : MaximalSpectrum (AdjoinRoot f)) (x : AdjoinRoot f) :
    maximalFactorQuotientEquiv f hf m (Ideal.Quotient.mk m.asIdeal x) =
      Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
        (maximalFactorIndexEquiv f hf m).2) x :=
  rfl

variable (p h : k[X]) [Fact (Irreducible p)] [Fact (Irreducible h)]

local notation "E" => AdjoinRoot p
local notation "H" => AdjoinRoot h
local notation "hE" => h.map (algebraMap k E)
local notation "pH" => p.map (algebraMap k H)

/-- Tensor swap reindexes the complete existing native factor indices. -/
def tensorSwapFactorIndexEquiv :
    {q : Σ d : ℕ, MonicIrreducibleOfDegree E d // poly q.2 ∣ hE} ≃
      {r : Σ d : ℕ, MonicIrreducibleOfDegree H d // poly r.2 ∣ pH} :=
  (maximalFactorIndexEquiv hE
    (Polynomial.map_ne_zero (Fact.out : Irreducible h).ne_zero)).symm.trans
      ((tensorSwapMaximalEquiv p h).trans (maximalFactorIndexEquiv pH
        (Polynomial.map_ne_zero (Fact.out : Irreducible p).ne_zero)))

/-- The factor bijection is the actual tensor swap on maximal ideals. -/
theorem tensorSwapFactorIndexEquiv_maximal
    (q : {q : Σ d : ℕ, MonicIrreducibleOfDegree E d // poly q.2 ∣ hE}) :
    nativeFactorMaximal pH (tensorSwapFactorIndexEquiv p h q) =
      tensorSwapMaximalEquiv p h (nativeFactorMaximal hE q) :=
  (maximalFactorIndexEquiv pH
    (Polynomial.map_ne_zero (Fact.out : Irreducible p).ne_zero)).symm_apply_apply _

/-- The literal factor kernels are matched by the actual whole-algebra map. -/
theorem tensorSwapFactorIndexEquiv_ker
    (q : {q : Σ d : ℕ, MonicIrreducibleOfDegree E d // poly q.2 ∣ hE}) :
    RingHom.ker (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
        (tensorSwapFactorIndexEquiv p h q).2)) =
      (RingHom.ker (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr q.2))).map
          (tensorSwapEquiv p h).toRingHom := by
  change (nativeFactorMaximal pH (tensorSwapFactorIndexEquiv p h q)).asIdeal =
    (nativeFactorMaximal hE q).asIdeal.map (tensorSwapEquiv p h).toRingHom
  rw [tensorSwapFactorIndexEquiv_maximal, tensorSwapMaximalEquiv_asIdeal]

/-- Matched native factors have their actual quotient fields identified. -/
def tensorSwapFactorQuotientEquiv
    (q : {q : Σ d : ℕ, MonicIrreducibleOfDegree E d // poly q.2 ∣ hE}) :
    AdjoinRoot (poly q.1.2) ≃+*
      AdjoinRoot (poly (tensorSwapFactorIndexEquiv p h q).1.2) := by
  let F : AdjoinRoot hE →+* AdjoinRoot (poly q.1.2) :=
    Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr q.2)
  exact (F.quotientKerEquivOfSurjective (Ideal.Quotient.factor_surjective _)).symm.trans
    ((tensorSwapQuotientEquiv p h (nativeFactorMaximal hE q)).trans
      (maximalFactorQuotientEquiv pH
        (Polynomial.map_ne_zero (Fact.out : Irreducible p).ne_zero)
        (tensorSwapMaximalEquiv p h (nativeFactorMaximal hE q))))

/-- The matched quotient equivalence retains the whole tensor-swap square. -/
theorem tensorSwapFactorQuotientEquiv_factor
    (q : {q : Σ d : ℕ, MonicIrreducibleOfDegree E d // poly q.2 ∣ hE})
    (x : AdjoinRoot hE) :
    tensorSwapFactorQuotientEquiv p h q
        (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr q.2) x) =
      Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
        (tensorSwapFactorIndexEquiv p h q).2) (tensorSwapEquiv p h x) := by
  let F : AdjoinRoot hE →+* AdjoinRoot (poly q.1.2) :=
    Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr q.2)
  have hF : Function.Surjective F := Ideal.Quotient.factor_surjective _
  let m : MaximalSpectrum (AdjoinRoot hE) := nativeFactorMaximal hE q
  let m' : MaximalSpectrum (AdjoinRoot pH) := tensorSwapMaximalEquiv p h m
  let e : (AdjoinRoot hE ⧸ m.asIdeal) ≃+* AdjoinRoot (poly q.1.2) :=
    F.quotientKerEquivOfSurjective hF
  have he : e.symm (F x) = Ideal.Quotient.mk m.asIdeal x :=
    RingHom.quotientKerEquivOfSurjective_symm_apply hF x
  have hswap : tensorSwapQuotientEquiv p h m (e.symm (F x)) =
      Ideal.Quotient.mk m'.asIdeal (tensorSwapEquiv p h x) :=
    (congrArg (tensorSwapQuotientEquiv p h m) he).trans
      (tensorSwapQuotientEquiv_mk p h m x)
  change maximalFactorQuotientEquiv pH
    (Polynomial.map_ne_zero (Fact.out : Irreducible p).ne_zero) m'
      (tensorSwapQuotientEquiv p h m (e.symm (F x))) = _
  exact (congrArg (maximalFactorQuotientEquiv pH
    (Polynomial.map_ne_zero (Fact.out : Irreducible p).ne_zero) m') hswap).trans
      (maximalFactorQuotientEquiv_mk pH
        (Polynomial.map_ne_zero (Fact.out : Irreducible p).ne_zero) m'
        (tensorSwapEquiv p h x))

end AdjoinRoot
