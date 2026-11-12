/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.RingTheory.Multiplicity.PrincipalEuler.QuotientTor
public import Colib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.EndpointOrder
public import Colib.AlgebraicGeometry.Divisors.SectionKernelDifferencePullback
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.UFDExtension
public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk

/-!
# Weighted local quotient Tor at the original polynomial endpoints

The endpoint is an actual Cartier section of the smooth polynomial projection.
Its stalk kernel therefore has a regular generator. Nonvanishing of the
specialized equation proves regularity of the face on the full principal
quotient. Native local Tor associativity then gives its whole cut length.

The first Tor module is the actual endpoint stalk restricted along its literal
stalk map; the second is the ambient local prime quotient. Identifying
them with correspondence graph incidence Tor, including the finite-image
residue degrees and all image collisions, remains a separate comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Order
open AlgebraicGeometry.PrincipalFamilyUnitOpen
open scoped BigOperators

universe u

namespace AlgebraicGeometry.PrincipalFamilyEndpointCuts

variable {k : Type u} [Field k] {W : Scheme.{u}} (p : W ⟶ Spec (.of k))

/-- The unchanged polynomial projection is a smooth relative curve. -/
theorem projection_smoothOfRelativeDimension : SmoothOfRelativeDimension 1 (projection p) := by
  have hpoly : SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))) := by
    rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
    apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
    have : Algebra.IsStandardSmoothOfRelativeDimension 1 k (MvPolynomial PUnit.{1} k) :=
      (Algebra.SubmersivePresentation.mvPolynomial.{0} k PUnit).isStandardSmoothOfRelativeDimension
        (by simp [Algebra.Presentation.dimension])
    have h : Algebra.IsStandardSmoothOfRelativeDimension 1 k (Polynomial k) :=
      Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv (n := 1)
        (MvPolynomial.uniqueAlgEquiv k PUnit.{1})
    rwa [← RingHom.isStandardSmoothOfRelativeDimension_algebraMap] at h
  exact (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
    (IsPullback.of_hasPullback _ _).flip hpoly

/-- The actual endpoint's kernel is Cartier, independently of the principal supports. -/
theorem endpoint_kernel_cartier (c : k) :
    Stacks.Divisors.IsEffectiveCartierDivisor (endpoint p c).ker := by
  have : IsAffineHom (projection p) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @IsAffineHom) (IsPullback.of_hasPullback _ _).flip inferInstance
  have := projection_smoothOfRelativeDimension p
  exact Stacks.Divisors.isEffectiveCartierDivisor_sectionKernel
    (projection p) (endpoint p c) (endpoint_projection p c)

private theorem endpoint_closed_immersion (c : k) : IsClosedImmersion (endpoint p c) := by
  have : IsAffineHom (projection p) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @IsAffineHom) (IsPullback.of_hasPullback _ _).flip inferInstance
  have : IsClosedImmersion (endpoint p c ≫ projection p) := by
    rw [endpoint_projection]
    infer_instance
  exact IsClosedImmersion.of_comp (endpoint p c) (projection p)

/-- The local face equation is produced from the actual Cartier endpoint, not assumed. -/
theorem exists_regular_endpoint_stalk_kernel (c : k) (x : W) :
    ∃ t : (parameterSpace p).presheaf.stalk (endpoint p c x),
      IsSMulRegular ((parameterSpace p).presheaf.stalk (endpoint p c x)) t ∧
      t ∈ IsLocalRing.maximalIdeal ((parameterSpace p).presheaf.stalk (endpoint p c x)) ∧
      RingHom.ker ((endpoint p c).stalkMap x).hom = Ideal.span {t} := by
  have := endpoint_closed_immersion p c
  obtain ⟨t, ht, hker⟩ := exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor
    (endpoint p c).ker (endpoint_kernel_cartier p c) (endpoint p c x)
  rw [IdealSheafData.stalk_ker_of_isClosedImmersion] at hker
  refine ⟨t, ht.isSMulRegular, ?_, hker⟩
  apply IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top ((endpoint p c).stalkMap x).hom)
  rw [hker]
  exact Ideal.subset_span (Set.mem_singleton t)

/-- The weighted actual endpoint stalk Tor sum retains all local principal multiplicities.
It has not yet been identified with the graph-incidence coefficient. -/
def weightedEndpointStalkTor (c : k) (x : W) (s : Γ(parameterSpace p, ⊤)) : ℤ :=
  let R := (parameterSpace p).presheaf.stalk (endpoint p c x)
  let n := (parameterSpace p).presheaf.germ ⊤ (endpoint p c x) (by trivial) s
  let φ := ((endpoint p c).stalkMap x).hom
  ∑ᶠ q ∈ {q : PrimeSpectrum R | Minimal (· ∈ Module.support R (R ⧸ Ideal.span {n})) q},
    ((Module.length (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl (R ⧸ Ideal.span {n}))).toNat : ℤ) *
    (∑ i ∈ Finset.range 2, (-1 : ℤ) ^ i *
      ((Module.length R (((Tor (ModuleCat R) i).obj
      ((ModuleCat.restrictScalars φ).obj (ModuleCat.of (W.presheaf.stalk x)
        (W.presheaf.stalk x)))).obj
        (ModuleCat.of R (R ⧸ q.asIdeal)))).toNat : ℤ))

/-- Local weighted actual quotient Tor is the full endpoint cut length.
The nonzero specialized germ supplies component regularity through the full quotient. -/
@[colib_tag "COL-1045",
  colib_ref "axiom_stacks_5ed82d14"
    "StacksFrontier/AlgebraicGeometry/Divisors/EffectiveCartier/UFDExtension.lean:155-164"
    "ingredient" "A regular generator of the actual Cartier endpoint stalk kernel",
  stacks 02QF "Ingredient: native local associativity for full principal quotient multiplicities"]
theorem weightedEndpointStalkTor_eq_cutLength
    [IsIntegral W] [IsNoetherian W] [IsNoetherian (parameterSpace p)]
    (c : k) (x : W) (hx : coheight x = 1) (s : Γ(parameterSpace p, ⊤))
    (hs : W.presheaf.germ ⊤ x (by trivial) ((endpoint p c).appTop s) ≠ 0) :
    weightedEndpointStalkTor p c x s = ((cutLength p c x s).toNat : ℤ) := by
  have := endpoint_closed_immersion p c
  obtain ⟨t, ht, htm, hker⟩ := exists_regular_endpoint_stalk_kernel p c x
  let n := (parameterSpace p).presheaf.germ ⊤ (endpoint p c x) (by trivial) s
  let φ := ((endpoint p c).stalkMap x).hom
  have hn : φ n ≠ 0 := by
    change (endpoint p c).stalkMap x n ≠ 0
    simpa only [n, endpoint_germ] using hs
  have hfinite : Module.length (W.presheaf.stalk x)
      ((W.presheaf.stalk x) ⧸ Ideal.span {φ n}) ≠ ⊤ := by
    rw [← Module.quotient_length_ker_sup_span φ ((endpoint p c).stalkMap_surjective x)]
    exact endpoint_cut_finite p c x hx s hs
  have h := Module.principal_quotient_tor_associativity_of_surjective
    φ ((endpoint p c).stalkMap_surjective x) t n ht htm hker hn hfinite 1
  unfold weightedEndpointStalkTor
  dsimp only
  simp_rw [← Module.length_tor_quotient_ker
    ((endpoint p c).stalkMap x).hom ((endpoint p c).stalkMap_surjective x)]
  rw [hker]
  rw [h]
  exact congrArg (fun l : ℕ∞ => (l.toNat : ℤ))
    (Module.quotient_length_ker_sup_span φ ((endpoint p c).stalkMap_surjective x) n).symm

/-- The signed local stalk Tor terms cancel at the original zero endpoint.
This does not yet assert equality of correspondence graph composites. -/
theorem weightedEndpointStalkTor_difference_zero
    [IsIntegral W] [IsNoetherian W] [IsNoetherian (parameterSpace p)]
    (a b : Γ(W, ⊤)) (x : W) (hx : coheight x = 1)
    (hb : W.presheaf.germ ⊤ x (by trivial) b ≠ 0) :
    weightedEndpointStalkTor p 0 x (numerator p a b) -
      weightedEndpointStalkTor p 0 x (denominator p b) = 0 := by
  rw [weightedEndpointStalkTor_eq_cutLength p 0 x hx _ (by simpa using hb),
    weightedEndpointStalkTor_eq_cutLength p 0 x hx _ (by simpa using hb),
    numerator_cutLength_zero, sub_self]

/-- At one the signed local stalk Tor sum is the native order of the same
original fraction. Both full principal quotients retain their multiplicities. -/
theorem weightedEndpointStalkTor_difference_one
    [IsIntegral W] [IsNoetherian W] [IsNoetherian (parameterSpace p)]
    (a b : Γ(W, ⊤)) (x : W) (hx : coheight x = 1)
    (ha : W.presheaf.germ ⊤ x (by trivial) a ≠ 0)
    (hb : W.presheaf.germ ⊤ x (by trivial) b ≠ 0) :
    weightedEndpointStalkTor p 1 x (numerator p a b) -
      weightedEndpointStalkTor p 1 x (denominator p b) =
      W.ord (algebraMap (W.presheaf.stalk x) W.functionField
          (W.presheaf.germ ⊤ x (by trivial) a) /
        algebraMap (W.presheaf.stalk x) W.functionField
          (W.presheaf.germ ⊤ x (by trivial) b)) x := by
  rw [weightedEndpointStalkTor_eq_cutLength p 1 x hx _ (by simpa using ha),
    weightedEndpointStalkTor_eq_cutLength p 1 x hx _ (by simpa using hb)]
  exact signedCutCoefficient_one p a b x hx ha hb

end AlgebraicGeometry.PrincipalFamilyEndpointCuts
