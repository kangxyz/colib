/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Algebra.Category.ModuleCat.Tor.LocalizedMiddleDiagonal.Length
public import Colib.AlgebraicGeometry.Chow.FlatComponentCoefficient
public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleRegularImmersion
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.Diagram
public import Colib.RingTheory.Koszul.GenericEuler
public import Colib.RingTheory.Koszul.RestrictionComparison
public import StacksFrontier.Homology.Tor.Independence
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.CoefficientColength
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.StalkPrimes
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ClosedImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.Support
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.Flatness.StalkIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToDiagonal.LocalMultiplicity
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.PerfectFactor
public import StacksFrontier.RingTheory.Koszul.Localization
public import StacksFrontier.RingTheory.Koszul.TorComparison.QuotientTor
public import StacksFrontier.RingTheory.Length.RingEquiv

/-!
# Local Koszul dévissage at a generic Cartesian intersection

At a generic point of a Cartesian intersection with a closed subscheme, the mapped generators
of the closed subscheme's stalk ideal generate an ideal of definition in the full support stalk.
The Koszul Euler characteristic therefore decomposes over the original minimal primes of that
stalk, with their full localized lengths.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme
open RingTheory.Sequence Stacks.AlgebraicGeometry.RegularIdealSheaf
open scoped TensorProduct

universe u

namespace Stacks.Chow

/-- The Koszul Euler sum can be written over all degrees because its homology vanishes
above the length of the list. -/
theorem seqEuler_eq_finsum_homology_length {R M : Type u} [CommRing R] [AddCommGroup M]
    [Module R M] {r : ℕ} (s : Fin r → R) :
    Koszul.seqEuler s M = ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      ((Module.length R ((Koszul.seqComplexTensor s M).homology n)).toNat : ℤ) := by
  classical
  let a : ℕ → ℤ := fun n => (-1 : ℤ) ^ n *
    ((Module.length R ((Koszul.seqComplexTensor s M).homology n)).toNat : ℤ)
  have hsupport : Function.support a ⊆ (Finset.range (r + 1) : Set ℕ) := by
    intro n hn
    by_contra h
    have hr : r < n := by
      exact Nat.lt_of_succ_le (by simpa only [Finset.coe_range, Set.mem_Iio, not_lt] using h)
    have : Subsingleton (⋀[R]^n (Fin r → R)) :=
      exteriorPower.subsingleton_of_span_eq_top_of_card_lt
        (Pi.basisFun R (Fin r)) (Pi.basisFun R (Fin r)).span_eq n (by simpa using hr)
    have hz : IsZero (ModuleCat.of R ((⋀[R]^n (Fin r → R)) ⊗[R] M)) :=
      ModuleCat.isZero_of_subsingleton _
    have hh : IsZero ((Koszul.seqComplexTensor s M).homology n) :=
      ((Koszul.seqComplexTensor s M).sc n).isZero_homology_of_isZero_X₂ hz
    have : Subsingleton ((Koszul.seqComplexTensor s M).homology n) :=
      ModuleCat.subsingleton_of_isZero hh
    exact hn (by simp [a])
  change (∑ n : Fin (r + 1), a n) = ∑ᶠ n : ℕ, a n
  rw [finsum_eq_sum_of_support_subset a hsupport, Fin.sum_univ_eq_sum_range]

/-- When a regular list generates the ambient diagonal ideal, its image on a quotient support
computes the signed categorical Tor length, with the original ambient length preserved. -/
theorem finsum_tor_length_eq_mapped_seqEuler {A R : Type u} [CommRing A] [CommRing R]
    [Algebra A R] (hφ : Function.Surjective (algebraMap A R)) {r : ℕ} (s : Fin r → A)
    (hs : RingTheory.Sequence.IsRegular A (List.ofFn s)) (J : Ideal A)
    (hJ : J = Ideal.span (Set.range s)) :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * ((Module.length A
      (((CategoryTheory.Tor (ModuleCat.{u} A) n).obj
        ((ModuleCat.restrictScalars (algebraMap A R)).obj (ModuleCat.of R R))).obj
          (ModuleCat.of A (A ⧸ J)))).toNat : ℤ)) =
      Koszul.seqEuler (fun t => algebraMap A R (s t)) R := by
  rw [seqEuler_eq_finsum_homology_length]
  refine finsum_congr fun n => ?_
  let R₀ := (ModuleCat.restrictScalars (algebraMap A R)).obj (ModuleCat.of R R)
  let H := (Koszul.seqComplexTensor (fun t => algebraMap A R (s t)) R).homology n
  let H₀ := (ModuleCat.restrictScalars (algebraMap A R)).obj H
  let e := (((Tor_iso_Tor' A n) ≪≫ (torFlip_iso_Tor' A n).symm).app R₀).app
        (ModuleCat.of A (A ⧸ J)) ≪≫
      Koszul.torIsoHomologySeqComplexTensorOfIsRegular s hs J hJ R₀ n ≪≫
    Koszul.homologySeqComplexTensorRestrictScalarsIso s (ModuleCat.of R R) n
  let : IsScalarTower A R H₀ := IsScalarTower.of_compHom A R H
  have hlen : Module.length A H₀ = Module.length R H :=
    Module.length_eq_of_surjective (R := R) (M := H₀) hφ
  rw [e.toLinearEquiv.length_eq, hlen]

/-- The weight at a minimal prime of a support stalk is the length of the actual stalk at
the corresponding generic support point. -/
theorem length_localizedSupportStalk_eq_length_stalk {P : Scheme.{u}} (z : P)
    (p : PrimeSpectrum (P.presheaf.stalk z)) :
    Module.length (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl (P.presheaf.stalk z)) =
      Module.length (P.presheaf.stalk (P.fromSpecStalk z p))
        (P.presheaf.stalk (P.fromSpecStalk z p)) := by
  let A := P.presheaf.stalk z
  let Aₚ := Localization.AtPrime p.asIdeal
  let B := P.presheaf.stalk (P.fromSpecStalk z p)
  have h : P.fromSpecStalk z p ⤳ z := P.range_fromSpecStalk.subset ⟨p, rfl⟩
  let : Algebra A B := (P.presheaf.stalkSpecializes h).hom.toAlgebra
  have : IsLocalization.AtPrime B p.asIdeal := isLocalization_stalk_of_specializes h p rfl
  let e : LocalizedModule p.asIdeal.primeCompl A ≃ₗ[A] Aₚ :=
    IsLocalizedModule.linearEquiv p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl A) (Algebra.linearMap A Aₚ)
  exact (e.extendScalarsOfIsLocalization p.asIdeal.primeCompl Aₚ).length_eq.trans
    (Module.length_eq_of_ringEquiv
      (IsLocalization.algEquiv p.asIdeal.primeCompl Aₚ B).toRingEquiv)

/-- A minimal prime of the support stalk gives the actual generic support point selected by
the canonical map from the spectrum of that stalk. -/
def genericSupportPointOfMinimalStalkPrime {P : Scheme.{u}} (z : P)
    (p : {p : PrimeSpectrum (P.presheaf.stalk z) // IsMin p}) : genericPoints P :=
  ⟨P.fromSpecStalk z p.1, by
    have hη : P.fromSpecStalk z p.1 ⤳ z := P.range_fromSpecStalk.subset ⟨p.1, rfl⟩
    refine (mem_genericPoints_iff_forall_specializes_eq _).2 fun y hy => ?_
    have hyz : y ∈ Set.range (P.fromSpecStalk z) := by
      rw [P.range_fromSpecStalk]
      exact hy.trans hη
    obtain ⟨q, hq⟩ := hyz
    subst y
    let q' : PrimeSpectrum (P.presheaf.stalk z) := q
    have hqp : q' ≤ p.1 := (PrimeSpectrum.le_iff_specializes q' p.1).2
      ((P.fromSpecStalk z).isEmbedding.isInducing.specializes_iff.mp hy)
    exact congrArg (fun r : PrimeSpectrum (P.presheaf.stalk z) => P.fromSpecStalk z r)
      (p.2.eq_of_le hqp)⟩

/-- The minimal primes are exactly the generic support points specializing to the chosen
support point. -/
def minimalStalkPrimeEquivGenericSupportPoints {P : Scheme.{u}} (z : P) :
    {p : PrimeSpectrum (P.presheaf.stalk z) // IsMin p} ≃
      {η : genericPoints P // η.1 ⤳ z} := by
  refine Equiv.ofBijective (fun p => ⟨genericSupportPointOfMinimalStalkPrime z p,
    P.range_fromSpecStalk.subset ⟨p.1, rfl⟩⟩) ⟨?_, ?_⟩
  · intro p q h
    exact Subtype.ext ((P.fromSpecStalk z).isEmbedding.injective
      (congrArg (fun η : {η : genericPoints P // η.1 ⤳ z} => η.1.1) h))
  · rintro ⟨⟨η, hη⟩, hηz⟩
    obtain ⟨p, hp⟩ : η ∈ Set.range (P.fromSpecStalk z) := by
      rw [P.range_fromSpecStalk]
      exact hηz
    let p' : PrimeSpectrum (P.presheaf.stalk z) := p
    have hp' : IsMin p' := by
      intro q hqp
      have hq := (PrimeSpectrum.le_iff_specializes q p').mp hqp
      have h := (mem_genericPoints_iff_forall_specializes_eq _).mp hη _
        ((hq.map (P.fromSpecStalk z).continuous).trans (specializes_of_eq hp))
      have he : q = p' := (P.fromSpecStalk z).isEmbedding.injective (h.trans hp.symm)
      exact he.ge
    exact ⟨⟨p', hp'⟩, Subtype.ext (Subtype.ext hp)⟩

/-- The support point lies in the actual reduced component of any generic point
specializing to it. -/
def genericSupportComponentPoint {P : Scheme.{u}} (z : P)
    (η : {η : genericPoints P // η.1 ⤳ z}) :
    (integralComponentAt η.1.1).subscheme :=
  ⟨z, by
    change z ∈ ((integralComponentAt η.1.1).support : Set P)
    rw [coe_support_integralComponentAt]
    exact η.2.mem_closure⟩

/-- The prime quotient contribution is the Koszul Euler characteristic of the actual
reduced component stalk, with scalars given by its closed immersion. -/
theorem seqEuler_quotient_eq_integralComponentStalk {P : Scheme.{u}} (z : P)
    (p : {p : PrimeSpectrum (P.presheaf.stalk z) // IsMin p}) {r : ℕ}
    (s : Fin r → P.presheaf.stalk z) :
    let η := minimalStalkPrimeEquivGenericSupportPoints z p
    let y := genericSupportComponentPoint z η
    let W := integralComponentAt η.1.1
    Koszul.seqEuler s (P.presheaf.stalk z ⧸ p.1.asIdeal) =
      Koszul.seqEuler (fun j => (W.subschemeι.stalkMap y).hom (s j))
        (W.subscheme.presheaf.stalk y) := by
  dsimp only
  let η := minimalStalkPrimeEquivGenericSupportPoints z p
  let W := integralComponentAt η.1.1
  let y := genericSupportComponentPoint z η
  let A := P.presheaf.stalk z
  let B := W.subscheme.presheaf.stalk y
  let φ : A →+* B := (W.subschemeι.stalkMap y).hom
  let : Algebra A B := φ.toAlgebra
  have hφ : Function.Surjective φ := SurjectiveOnStalks.stalkMap_surjective W.subschemeι y
  have hk : RingHom.ker φ = p.1.asIdeal := by
    change RingHom.ker (W.subschemeι.stalkMap y).hom = _
    rw [ker_stalkMap_eq_idealStalk_ker, W.ker_subschemeι]
    change IdealSheafData.stalk (integralComponentAt (P.fromSpecStalk z p.1)) z = _
    exact idealStalk_vanishingIdeal_closure_fromSpecStalk z p.1
  let e : (A ⧸ p.1.asIdeal) ≃ₐ[A] B := by
    rw [← hk]
    exact Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A B) hφ
  change Koszul.seqEuler s (A ⧸ p.1.asIdeal) =
    Koszul.seqEuler (fun j => φ (s j)) B
  unfold Koszul.seqEuler
  refine Finset.sum_congr rfl fun n _ => ?_
  let H := (Koszul.seqComplexTensor (fun j => φ (s j)) B).homology (n : ℕ)
  let : Module A H := Module.compHom H φ
  have : IsScalarTower A B H := IsScalarTower.of_compHom A B H
  let eH : (Koszul.seqComplexTensor s (A ⧸ p.1.asIdeal)).homology (n : ℕ) ≃ₗ[A] H :=
    (Koszul.homologyTensorCongr s e.toLinearEquiv n ≪≫
      Koszul.homologySeqComplexTensorRestrictScalarsIso s (ModuleCat.of B B) n).toLinearEquiv
  rw [eH.length_eq, Module.length_eq_of_surjective (M := H) hφ]

variable {C P D Q : Scheme.{u}} {i : C ⟶ P} {g : C ⟶ D} {f : P ⟶ Q} {j : D ⟶ Q}
  [IsClosedImmersion j] [IsLocallyNoetherian P]
  (sq : IsPullback i g f j) (x : genericPoints C)

include sq in
omit [IsClosedImmersion j] [IsLocallyNoetherian P] in
/-- The closed pullback has the indicated equality of ambient points. -/
theorem cartesianIntersection_genericPoint_eq : j (g x.1) = f (i x.1) := by
  simpa only [Scheme.Hom.comp_apply] using congrArg (fun m : C ⟶ Q => m x.1) sq.w.symm

/-- The ambient-to-support stalk map, using the equality of ambient points in the square. -/
abbrev cartesianIntersectionGenericStalkMap :
    Q.presheaf.stalk (j (g x.1)) →+* P.presheaf.stalk (i x.1) :=
  ((Q.presheaf.stalkCongr (Inseparable.of_eq (cartesianIntersection_genericPoint_eq sq x))).hom ≫
    f.stalkMap (i x.1)).hom

set_option quotPrecheck false in
local notation "R" => P.presheaf.stalk (i x.1)
local notation "a" => cartesianIntersectionGenericStalkMap sq x

/-- The mapped list generates the actual local pullback ideal, which has finite colength at the
generic point of the entire intersection. -/
theorem isIdealOfDefinition_mapped_cartesianIntersection_stalk {r : ℕ}
    (s : Fin r → Q.presheaf.stalk (j (g x.1)))
    (hs : IdealSheafData.stalk j.ker (j (g x.1)) = Ideal.span (Set.range s)) :
    IsIdealOfDefinition (Ideal.span (Set.range (fun t => a (s t)))) := by
  let : IsClosedImmersion i := MorphismProperty.of_isPullback sq.flip inferInstance
  let : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian i
  let : IsArtinianRing (C.presheaf.stalk x.1) := generic_stalk_artinian x
  have hk := Stacks.Flatness.ker_stalkMap_of_isPullback sq x.1
    (cartesianIntersection_genericPoint_eq sq x)
  rw [ker_stalkMap_eq_idealStalk_ker j (g x.1), hs, Ideal.map_span, ← Set.range_comp'] at hk
  change RingHom.ker (i.stalkMap x.1).hom = Ideal.span (Set.range (fun t => a (s t))) at hk
  rw [← hk]
  change Ideal.radical (RingHom.ker (i.stalkMap x.1).hom) = IsLocalRing.maximalIdeal R
  rw [RingHom.ker_eq_comap_bot, ← Ideal.comap_radical,
    ← IsArtinianRing.jacobson_eq_radical, IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top,
    IsLocalRing.maximalIdeal_comap]

/-- The Koszul Euler coefficient at the generic point of the entire Cartesian intersection
is the weighted sum over the original minimal primes of the support stalk. -/
theorem seqEuler_mapped_cartesianIntersection_eq_finsum_minimalPrimes {r : ℕ}
    (s : Fin r → Q.presheaf.stalk (j (g x.1)))
    (hs : IdealSheafData.stalk j.ker (j (g x.1)) = Ideal.span (Set.range s)) :
    Koszul.seqEuler (fun t => a (s t)) R =
      ∑ᶠ p : {p : PrimeSpectrum R // IsMin p},
        ((Module.length (Localization.AtPrime p.1.asIdeal)
          (LocalizedModule p.1.asIdeal.primeCompl R)).toNat : ℤ) *
          Koszul.seqEuler (fun t => a (s t)) (R ⧸ p.1.asIdeal) :=
  Koszul.seqEuler_eq_finsum_minimalPrimes _ _
    (isIdealOfDefinition_mapped_cartesianIntersection_stalk sq x s hs)

/-- The same dévissage with each weight read as the structure length at the corresponding
generic point of the full support scheme. -/
theorem seqEuler_mapped_cartesianIntersection_eq_finsum_genericStalkLengths {r : ℕ}
    (s : Fin r → Q.presheaf.stalk (j (g x.1)))
    (hs : IdealSheafData.stalk j.ker (j (g x.1)) = Ideal.span (Set.range s)) :
    Koszul.seqEuler (fun t => a (s t)) R =
      ∑ᶠ p : {p : PrimeSpectrum R // IsMin p},
        let η := genericSupportPointOfMinimalStalkPrime (i x.1) p
        ((Module.length (P.presheaf.stalk η.1) (P.presheaf.stalk η.1)).toNat : ℤ) *
          Koszul.seqEuler (fun t => a (s t)) (R ⧸ p.1.asIdeal) := by
  rw [seqEuler_mapped_cartesianIntersection_eq_finsum_minimalPrimes sq x s hs]
  refine finsum_congr fun p => ?_
  rw [length_localizedSupportStalk_eq_length_stalk]
  rfl

/-- The weighted Euler sum over the actual reduced components through the intersection point. -/
theorem seqEuler_mapped_cartesianIntersection_eq_finsum_genericComponents {r : ℕ}
    (s : Fin r → Q.presheaf.stalk (j (g x.1)))
    (hs : IdealSheafData.stalk j.ker (j (g x.1)) = Ideal.span (Set.range s)) :
    Koszul.seqEuler (fun t => a (s t)) R =
      ∑ᶠ η : {η : genericPoints P // η.1 ⤳ i x.1},
        let W := integralComponentAt η.1.1
        let y := genericSupportComponentPoint (i x.1) η
        ((Module.length (P.presheaf.stalk η.1.1) (P.presheaf.stalk η.1.1)).toNat : ℤ) *
          Koszul.seqEuler (fun t => (W.subschemeι.stalkMap y).hom (a (s t)))
            (W.subscheme.presheaf.stalk y) := by
  rw [seqEuler_mapped_cartesianIntersection_eq_finsum_genericStalkLengths sq x s hs,
    ← finsum_comp_equiv (minimalStalkPrimeEquivGenericSupportPoints (i x.1))]
  refine finsum_congr fun p => ?_
  exact congrArg (_ * ·)
    (seqEuler_quotient_eq_integralComponentStalk (i x.1) p (fun t => a (s t)))

/-- The signed ambient Tor coefficient of two structure modules with specified scalar maps. -/
def structureTorCoefficient {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (α : A →+* B) (β : A →+* C) : ℤ :=
  let M := (ModuleCat.restrictScalars α).obj (ModuleCat.of B B)
  let N := (ModuleCat.restrictScalars β).obj (ModuleCat.of C C)
  ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
    ((Module.length A (((Tor (ModuleCat.{u} A) n).obj M).obj N)).toNat : ℤ)

/-- Isomorphic ambient and support local rings preserve each signed Tor length, with both
specified scalar maps. -/
theorem structureTorCoefficient_eq_of_ringEquiv
    {A B C A' B' C' : Type u}
    [CommRing A] [CommRing B] [CommRing C] [CommRing A'] [CommRing B'] [CommRing C']
    (α : A →+* B) (β : A →+* C) (α' : A' →+* B') (β' : A' →+* C')
    (e : A ≃+* A') (l : B ≃+* B') (r : C ≃+* C')
    (hl : l.toRingHom.comp α = α'.comp e.toRingHom)
    (hr : r.toRingHom.comp β = β'.comp e.toRingHom) :
    structureTorCoefficient α β = structureTorCoefficient α' β' := by
  let M := (ModuleCat.restrictScalars α).obj (ModuleCat.of B B)
  let N := (ModuleCat.restrictScalars β).obj (ModuleCat.of C C)
  let M' := (ModuleCat.restrictScalars α').obj (ModuleCat.of B' B')
  let N' := (ModuleCat.restrictScalars β').obj (ModuleCat.of C' C')
  let F := ModuleCat.restrictScalars e.toRingHom
  let eM : M ≅ F.obj M' :=
    LinearEquiv.toModuleIso (X₁ := M) (X₂ := F.obj M')
      (AddEquiv.toLinearEquiv l.toAddEquiv (fun x y => by
        let y₀ : B := y
        change l (α x * y₀) = α' (e x) * l y₀
        rw [map_mul]
        exact congrArg (· * l y₀) (DFunLike.congr_fun hl x)))
  let eN : N ≅ F.obj N' :=
    LinearEquiv.toModuleIso (X₁ := N) (X₂ := F.obj N')
      (AddEquiv.toLinearEquiv r.toAddEquiv (fun x y => by
        let y₀ : C := y
        change r (β x * y₀) = β' (e x) * r y₀
        rw [map_mul]
        exact congrArg (· * r y₀) (DFunLike.congr_fun hr x)))
  unfold structureTorCoefficient
  dsimp only
  refine finsum_congr fun n => ?_
  let eTor := ((Tor (ModuleCat A) n).mapIso eM).app N ≪≫
    ((Tor (ModuleCat A) n).obj (F.obj M')).mapIso eN ≪≫
    RingTheory.TorIndependence.torRestrictIso e M' N' n
  rw [eTor.toLinearEquiv.length_eq, ModuleCat.length_restrictScalars_of_surjective _
    e.surjective]

/-- The Koszul list for the second structure quotient computes its native Tor with the first
structure quotient. -/
theorem structureTorCoefficient_eq_seqEuler {A B C : Type u} [CommRing A] [CommRing B]
    [CommRing C] (α : A →+* B) (β : A →+* C)
    (hα : Function.Surjective α) (hβ : Function.Surjective β) {r : ℕ} (s : Fin r → A)
    (hsr : IsRegular A (List.ofFn s)) (hs : RingHom.ker β = Ideal.span (Set.range s)) :
    structureTorCoefficient α β = Koszul.seqEuler (fun t => α (s t)) B := by
  let : Algebra A B := α.toAlgebra
  let M := (ModuleCat.restrictScalars α).obj (ModuleCat.of B B)
  let e := Stacks.Intersection.Diagonal.kerQuotIso β hβ
  unfold structureTorCoefficient
  dsimp only
  refine Eq.trans (finsum_congr fun n => ?_)
    (finsum_tor_length_eq_mapped_seqEuler hα s hsr (RingHom.ker β) hs)
  let eTor := ((Tor (ModuleCat.{u} A) n).obj M).mapIso e
  exact congrArg (fun l : ℕ∞ => (-1 : ℤ) ^ n * (l.toNat : ℤ))
    eTor.toLinearEquiv.length_eq.symm

/-- The whole signed Tor coefficient is the weighted sum of native Tor coefficients of the
actual reduced support components through the generic intersection point. -/
theorem structureTorCoefficient_eq_finsum_cartesianIntersectionComponents
    [IsClosedImmersion f] {r : ℕ}
    (s : Fin r → Q.presheaf.stalk (j (g x.1)))
    (hsr : IsRegular (Q.presheaf.stalk (j (g x.1))) (List.ofFn s))
    (hs : IdealSheafData.stalk j.ker (j (g x.1)) = Ideal.span (Set.range s)) :
    structureTorCoefficient a (j.stalkMap (g x.1)).hom =
      ∑ᶠ η : {η : genericPoints P // η.1 ⤳ i x.1},
        let W := integralComponentAt η.1.1
        let y := genericSupportComponentPoint (i x.1) η
        ((Module.length (P.presheaf.stalk η.1.1) (P.presheaf.stalk η.1.1)).toNat : ℤ) *
          structureTorCoefficient ((W.subschemeι.stalkMap y).hom.comp a)
            (j.stalkMap (g x.1)).hom := by
  have hsurj : Function.Surjective (a) :=
    (f.stalkMap_surjective (i x.1)).comp
      (ConcreteCategory.bijective_of_isIso
        (Q.presheaf.stalkCongr
          (Inseparable.of_eq (cartesianIntersection_genericPoint_eq sq x))).hom).2
  have hk := (ker_stalkMap_eq_idealStalk_ker j (g x.1)).trans hs
  rw [structureTorCoefficient_eq_seqEuler a _ hsurj (j.stalkMap_surjective (g x.1)) s hsr hk,
    seqEuler_mapped_cartesianIntersection_eq_finsum_genericComponents sq x s hs]
  refine finsum_congr fun η => ?_
  dsimp only
  let W := integralComponentAt η.1.1
  let y := genericSupportComponentPoint (i x.1) η
  let φ := (W.subschemeι.stalkMap y).hom
  have hφ : Function.Surjective φ := W.subschemeι.stalkMap_surjective y
  have hβ : Function.Surjective (φ.comp a) := hφ.comp hsurj
  exact congrArg (_ * ·)
    (structureTorCoefficient_eq_seqEuler (φ.comp a) _ hβ
      (j.stalkMap_surjective (g x.1)) s hsr hk).symm

end Stacks.Chow

namespace Stacks.Chow

variable {k : Type u} [Field k] (X Y Z U V W : SmoothSite (Spec (.of k)))
  (p₁ : pullback (C := Scheme) X.hom Y.hom)
  (p₂ : pullback (C := Scheme) Y.hom Z.hom)
  (q₁ : pullback (C := Scheme) U.hom V.hom)
  (q₂ : pullback (C := Scheme) V.hom W.hom)

local notation "l" => correspondenceExteriorTarget X Y U V
  (integralComponentAt p₁) (integralComponentAt q₁)
local notation "r" => correspondenceExteriorSource Y Z V W
  (integralComponentAt p₂) (integralComponentAt q₂)
local notation "e₁" => correspondenceExteriorInclusion X Y U V
  (integralComponentAt p₁) (integralComponentAt q₁)
local notation "e₂" => correspondenceExteriorInclusion Y Z V W
  (integralComponentAt p₂) (integralComponentAt q₂)
set_option quotPrecheck false in
local notation "f" => (SmoothSite.product X U).hom
set_option quotPrecheck false in
local notation "g" => (SmoothSite.product Y V).hom
set_option quotPrecheck false in
local notation "h" => (SmoothSite.product Z W).hom
local notation "L" => correspondenceExteriorWholeIncidence X Y Z U V W p₁ p₂ q₁ q₂
local notation "ι" => correspondenceExteriorWholeIncidenceInclusion X Y Z U V W p₁ p₂ q₁ q₂

/-- The full product of the two exterior supports, viewed in the composition ambient. -/
abbrev correspondenceExteriorWholeSupportProduct : Scheme.{u} :=
  pullback (l ≫ g) (r ≫ g)

local notation "H" => correspondenceExteriorWholeSupportProduct X Y Z U V W p₁ p₂ q₁ q₂

/-- The whole incidence enters its full product support by imposing the middle diagonal. -/
abbrev correspondenceExteriorWholeIncidenceToSupport : L ⟶ H := pullback.mapDesc l r g

/-- The full product support enters the actual four-factor composition ambient. -/
def correspondenceExteriorWholeSupportInclusion :
    H ⟶ correspondenceIntersectionAmbient f g h :=
  pullback.map _ _ _ _ e₁ e₂ (𝟙 _) (by
    rw [Category.comp_id, ← Category.assoc, correspondenceExteriorInclusion_snd]) (by
    rw [Category.comp_id, ← Category.assoc, correspondenceExteriorInclusion_fst])

local notation "v" => correspondenceExteriorWholeIncidenceToSupport X Y Z U V W p₁ p₂ q₁ q₂
local notation "w" => correspondenceExteriorWholeSupportInclusion X Y Z U V W p₁ p₂ q₁ q₂
local notation "δ" => correspondenceTripleInclusion f g h
local notation "m" => correspondenceMiddlePair f g h

/-- The whole support square is Cartesian over the actual ambient middle diagonal. -/
theorem correspondenceExteriorWholeIncidence_isPullback : IsPullback v ι w δ := by
  have hw : w ≫ m =
      pullback.map (l ≫ g) (r ≫ g) g g l r (𝟙 _)
        (Category.comp_id _) (Category.comp_id _) := by
    apply @pullback.hom_ext _ _ _ _ _ g g
    · rw [Category.assoc]
      simp only [pullback.map, pullback.lift_fst]
      rw [show m ≫ pullback.fst g g =
        pullback.fst (pullback.snd f g ≫ g) (pullback.fst g h ≫ g) ≫ pullback.snd f g from
          pullback.lift_fst _ _ _]
      simp only [correspondenceExteriorWholeSupportInclusion, pullback.map,
        pullback.lift_fst_assoc, Category.assoc, correspondenceExteriorInclusion_snd]
    · rw [Category.assoc]
      simp only [pullback.map, pullback.lift_snd]
      rw [show m ≫ pullback.snd g g =
        pullback.snd (pullback.snd f g ≫ g) (pullback.fst g h ≫ g) ≫ pullback.fst g h from
          pullback.lift_snd _ _ _]
      simp only [correspondenceExteriorWholeSupportInclusion, pullback.map,
        pullback.lift_snd_assoc, Category.assoc, correspondenceExteriorInclusion_fst]
  have hι : ι ≫ correspondenceTripleMiddle f g h = pullback.fst l r ≫ l := by
    simp only [correspondenceExteriorWholeIncidenceInclusion, correspondenceTripleMiddle,
      pullback.map, Category.assoc, pullback.lift_fst_assoc, correspondenceExteriorInclusion_snd]
  have hv₁ : v ≫ pullback.fst (l ≫ g) (r ≫ g) = pullback.fst l r :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have hv₂ : v ≫ pullback.snd (l ≫ g) (r ≫ g) = pullback.snd l r :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hc : v ≫ w = ι ≫ δ := by
    apply @pullback.hom_ext _ _ _ _ _ (pullback.snd f g ≫ g) (pullback.fst g h ≫ g)
    · simp only [Category.assoc, correspondenceTripleInclusion_fst,
        correspondenceExteriorWholeSupportInclusion, correspondenceExteriorWholeIncidenceInclusion,
        pullback.map, pullback.lift_fst, reassoc_of% hv₁]
    · simp only [Category.assoc, correspondenceTripleInclusion_snd,
        correspondenceExteriorWholeSupportInclusion, correspondenceExteriorWholeIncidenceInclusion,
        pullback.map, pullback.lift_snd, reassoc_of% hv₂]
  have hh : IsPullback v (ι ≫ correspondenceTripleMiddle f g h)
      (w ≫ m) (pullback.diagonal g) := by
    rw [hw, hι]
    exact (pullback_map_diagonal_isPullback l r g).flip
  exact hh.of_bot hc (correspondenceTriple_isPullback f g h).flip

instance correspondenceExteriorWholeSupportInclusion_isClosedImmersion
    [IsFinite (exteriorSupportSourceProjection X Y (integralComponentAt p₁))]
    [IsFinite (exteriorSupportSourceProjection Y Z (integralComponentAt p₂))]
    [IsFinite (exteriorSupportSourceProjection U V (integralComponentAt q₁))]
    [IsFinite (exteriorSupportSourceProjection V W (integralComponentAt q₂))] :
    IsClosedImmersion w := by
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    (inferInstanceAs (IsClosedImmersion e₁)) (inferInstanceAs (IsClosedImmersion e₂))
    (by rw [← Category.assoc, correspondenceExteriorInclusion_snd])
    (by rw [← Category.assoc, correspondenceExteriorInclusion_fst])

/-- A single regular list in the actual ambient generates its smooth middle-diagonal ideal. -/
theorem exists_correspondenceTripleInclusion_regularList
    (z : correspondenceTripleProduct f g h) :
    ∃ (n : ℕ) (s : Fin n →
      (correspondenceIntersectionAmbient f g h).presheaf.stalk (δ z)),
      IsRegular ((correspondenceIntersectionAmbient f g h).presheaf.stalk (δ z))
        (List.ofFn s) ∧
      IdealSheafData.stalk (δ).ker (δ z) = Ideal.span (Set.range s) := by
  have hd : IsRegularImmersion δ :=
    Stacks.AlgebraicGeometry.isRegularImmersion_of_isPullback_of_flat
      (correspondenceTriple_isPullback f g h).flip
      (Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_section
        (pullback.fst g g) (pullback.diagonal g) (pullback.diagonal_fst g))
  obtain ⟨s, hs, hker⟩ := exists_isRegular_ker_stalkMap_of_isRegularImmersion δ hd z
  refine ⟨s.length, s.get, by simpa only [List.ofFn_get] using hs, ?_⟩
  rw [← Ideal.ofList_ofFn, List.ofFn_get, hker, ker_stalkMap_eq_idealStalk_ker]

variable (hp₁ : IsFiniteCorrespondencePoint X.hom Y.hom p₁)
  (hp₂ : IsFiniteCorrespondencePoint Y.hom Z.hom p₂)
  (hq₁ : IsFiniteCorrespondencePoint U.hom V.hom q₁)
  (hq₂ : IsFiniteCorrespondencePoint V.hom W.hom q₂)

include hp₁ hp₂ hq₁ hq₂ in
/-- At a generic point of the whole exterior incidence, its actual ambient Tor coefficient
decomposes with the full support multiplicities. -/
theorem structureTorCoefficient_exteriorWhole_eq_finsum_genericComponents
    (x : genericPoints L) :
    let sq := correspondenceExteriorWholeIncidence_isPullback X Y Z U V W p₁ p₂ q₁ q₂
    let α := cartesianIntersectionGenericStalkMap
      (show IsPullback v ι w δ from sq) x
    let β := ((δ).stalkMap (ι x.1)).hom
    structureTorCoefficient α β =
      ∑ᶠ η : {η : genericPoints H // η.1 ⤳ v x.1},
        let C := integralComponentAt η.1.1
        let y := genericSupportComponentPoint (v x.1) η
        ((Module.length ((H).presheaf.stalk η.1.1) ((H).presheaf.stalk η.1.1)).toNat : ℤ) *
          structureTorCoefficient ((C.subschemeι.stalkMap y).hom.comp α) β := by
  dsimp only
  let : IsFinite (exteriorSupportSourceProjection X Y (integralComponentAt p₁)) := hp₁.1
  let : IsFinite (exteriorSupportSourceProjection Y Z (integralComponentAt p₂)) := hp₂.1
  let : IsFinite (exteriorSupportSourceProjection U V (integralComponentAt q₁)) := hq₁.1
  let : IsFinite (exteriorSupportSourceProjection V W (integralComponentAt q₂)) := hq₂.1
  let : IsLocallyNoetherian (correspondenceIntersectionAmbient f g h) :=
    isLocallyNoetherian_correspondenceIntersectionAmbient (S := Spec (.of k)) f g h
  let : IsLocallyNoetherian H := LocallyOfFiniteType.isLocallyNoetherian w
  obtain ⟨_, s, hsr, hs⟩ :=
    exists_correspondenceTripleInclusion_regularList X Y Z U V W (ι x.1)
  exact structureTorCoefficient_eq_finsum_cartesianIntersectionComponents
    (correspondenceExteriorWholeIncidence_isPullback X Y Z U V W p₁ p₂ q₁ q₂) x s hsr hs

end Stacks.Chow
