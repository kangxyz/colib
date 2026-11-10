/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Dedekind.AffineEndpointNormAllDegrees
public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenEquivariance
public import Colib.RingTheory.Localization.FiniteTypeResidue

/-!
# Actual ground-field norms on every original endpoint branch

Adapted from Aglib `Dedekind/AffineEndpointBaseNorm.lean`, revision
`4f65be4eafa8964bd1f7a83682e99aa8165bd418`, lines 23–114.
The endpoint dictionary is the native quotient-residue equivalence followed by
evaluation. Native simultaneous norm equivariance identifies every branch norm
with its actual ground-field norm. The concluding equality keeps every original
local order and works in degree zero as well as positive degrees.
-/

@[expose] public noncomputable section
namespace Stacks.Chow.DedekindResidue

open Polynomial PolynomialResidue PolynomialDedekindResidue IsLocalRing IsDedekindDomain
attribute [local instance] Classical.decEq polynomialPointResidueCharZero

universe u
variable (k S : Type u) [Field k] [CharZero k]
  [CommRing S] [IsDedekindDomain S] [Algebra k[X] S] [Module.Finite k[X] S]
  [Module.IsTorsionFree k[X] S] [Algebra k S] [IsScalarTower k k[X] S]

local instance finiteType : Algebra.FiniteType k S := Algebra.FiniteType.trans (S := k[X])
  (inferInstanceAs (Algebra.FiniteType k k[X]))
  (inferInstanceAs (Algebra.FiniteType k[X] S))

local instance localResidueFinite (q : HeightOneSpectrum S) :
    FiniteDimensional k (ResidueField (Localization.AtPrime q.asIdeal)) :=
  Localization.finiteType_localResidue_finite k S q.asIdeal

/-- The literal native residue dictionary and evaluation, as a base-field equivalence. -/
def endpointResidueEquiv (a : k) :
    ResidueField (Localization.AtPrime (point (endpointPolynomial k a)).asIdeal) ≃ₐ[k] k :=
  { linearResidueEquiv a with
    commutes' := linearResidueEquiv_algebraMap a }

/-- Every original branch norm becomes precisely its native norm to the ground field. -/
theorem endpoint_branchNorm_eq (a : k) (n : ℕ)
    (q : AdicCompletion.IdealBranch
      ((point (endpointPolynomial k a)).asIdeal.map (algebraMap k[X] S)))
    (x : MilnorKTheory (ResidueField (Localization.AtPrime
      (branchPoint k[X] S (point (endpointPolynomial k a)) q).asIdeal)) n) :
    milnorKTheoryMap (endpointResidueEquiv k a).toRingHom n
      (branchCoordinateNorm k[X] S (point (endpointPolynomial k a)) n q x) =
        milnorKNorm k (ResidueField (Localization.AtPrime
          (branchPoint k[X] S (point (endpointPolynomial k a)) q).asIdeal)) n x := by
  let p := point (endpointPolynomial k a)
  let := Localization.basePrimeLocalAlgebra p.asIdeal q.val
    (Localization.originalIdealBranch_under p q)
  let := Localization.basePrimeLocalTower p.asIdeal q.val
    (Localization.originalIdealBranch_under p q)
  let := Localization.basePrimeLocal_isLocalHom p.asIdeal q.val
    (Localization.originalIdealBranch_under p q)
  let := Localization.basePrimeLocal_residueFinite p.asIdeal q.val
    (Localization.originalIdealBranch_under p q)
  let : IsScalarTower k (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.val) := by
    apply IsScalarTower.of_algebraMap_eq
    intro c
    rw [IsScalarTower.algebraMap_apply k k[X] (Localization.AtPrime p.asIdeal),
      ← IsScalarTower.algebraMap_apply k[X] (Localization.AtPrime p.asIdeal),
      ← IsScalarTower.algebraMap_apply k k[X]]
  let : FiniteDimensional k (ResidueField (Localization.AtPrime q.val)) :=
    localResidueFinite k S (branchPoint k[X] S p q)
  have hs (c : ResidueField (Localization.AtPrime p.asIdeal)) :
      (RingEquiv.refl (ResidueField (Localization.AtPrime q.val)))
          (algebraMap (ResidueField (Localization.AtPrime p.asIdeal))
            (ResidueField (Localization.AtPrime q.val)) c) =
        algebraMap k (ResidueField (Localization.AtPrime q.val))
          (endpointResidueEquiv k a c) := by
    have hc : algebraMap k (ResidueField (Localization.AtPrime p.asIdeal))
        (endpointResidueEquiv k a c) = c :=
      ((endpointResidueEquiv k a).symm.commutes _).symm.trans
        ((endpointResidueEquiv k a).symm_apply_apply c)
    rw [IsScalarTower.algebraMap_apply k (ResidueField (Localization.AtPrime p.asIdeal)), hc]
    rfl
  let : CharZero (ResidueField (Localization.AtPrime p.asIdeal)) :=
    polynomialPointResidueCharZero k p
  let κQ := ResidueField (Localization.AtPrime q.val)
  have h := milnorKNorm_map_ringEquiv (endpointResidueEquiv k a).toRingEquiv
    (RingEquiv.refl κQ) (RingHom.ext hs) n x
  have htransport : milnorKTransport (RingEquiv.refl κQ).toRingHom n x = x :=
    milnorKTransport_id_apply (k₁ := κQ) n x
  have hnorm := congrArg (milnorKNorm k κQ n) htransport
  rw [milnorKTheoryMap_eq_transport]
  dsimp only [branchCoordinateNorm]
  simp only [AddMonoidHom.coe_toIntLinearMap]
  exact h.trans hnorm

variable (E : Type u) [Field E] [Algebra S E] [IsFractionRing S E]
  [Algebra k[X] E] [IsScalarTower k[X] S E]
  [Algebra (RatFunc k) E] [IsScalarTower k[X] (RatFunc k) E]
  [FiniteDimensional (RatFunc k) E]

omit [Algebra k[X] E] [IsScalarTower k[X] S E]
  [IsScalarTower k[X] (RatFunc k) E] [FiniteDimensional (RatFunc k) E] in
/-- The full endpoint sum has actual native ground-field norms term by term. -/
theorem endpointWeightedResidueSum_eq_baseNormSum (a : k) (n : ℕ) (u : Fin n → Sˣ) :
    endpointWeightedResidueSum k S E a n u =
      ∑ q : AdicCompletion.IdealBranch
          ((point (endpointPolynomial k a)).asIdeal.map (algebraMap k[X] S)),
        let Q := branchPoint k[X] S (point (endpointPolynomial k a)) q
        dvrFracOrd (IsDiscreteValuationRing.exists_irreducible
          (Localization.AtPrime Q.asIdeal)).choose_spec (endpointParameter k E a) •
          milnorKNorm k (ResidueField (Localization.AtPrime Q.asIdeal)) n
            (milnorKTupleSymbol (Units.map
              ((IsLocalRing.residue (Localization.AtPrime Q.asIdeal)).comp
                (algebraMap S (Localization.AtPrime Q.asIdeal))).toMonoidHom ∘ u)) := by
  let p := point (endpointPolynomial k a)
  let e : ResidueField (Localization.AtPrime p.asIdeal) →+* k :=
    (endpointResidueEquiv k a).toRingHom
  let T := milnorKTheoryMap e n
  let f : AdicCompletion.IdealBranch (p.asIdeal.map (algebraMap k[X] S)) →
      MilnorKTheory (ResidueField (Localization.AtPrime p.asIdeal)) n := fun q =>
    let Q := branchPoint k[X] S p q
    branchCoordinateNorm k[X] S p n q
      (dvrFracOrd (IsDiscreteValuationRing.exists_irreducible
        (Localization.AtPrime Q.asIdeal)).choose_spec (endpointParameter k E a) •
        milnorKTupleSymbol (Units.map
          ((IsLocalRing.residue (Localization.AtPrime Q.asIdeal)).comp
            (algebraMap S (Localization.AtPrime Q.asIdeal))).toMonoidHom ∘ u))
  have hmap : T (∑ q, f q) = ∑ q, T (f q) := map_sum T f Finset.univ
  refine hmap.trans ?_
  apply Finset.sum_congr rfl
  intro q _
  change milnorKTheoryMap (endpointResidueEquiv k a).toRingHom n _ = _
  rw [endpoint_branchNorm_eq, map_zsmul]

/-- Equality of the explicit original order-weighted ground-field norm sums in every degree. -/
theorem endpointBaseNormSum_eq_all (a b : k) (n : ℕ) (u : Fin n → Sˣ) :
    (∑ q : AdicCompletion.IdealBranch
        ((point (endpointPolynomial k a)).asIdeal.map (algebraMap k[X] S)),
      let Q := branchPoint k[X] S (point (endpointPolynomial k a)) q
      dvrFracOrd (IsDiscreteValuationRing.exists_irreducible
        (Localization.AtPrime Q.asIdeal)).choose_spec (endpointParameter k E a) •
        milnorKNorm k (ResidueField (Localization.AtPrime Q.asIdeal)) n
          (milnorKTupleSymbol (Units.map
            ((IsLocalRing.residue (Localization.AtPrime Q.asIdeal)).comp
              (algebraMap S (Localization.AtPrime Q.asIdeal))).toMonoidHom ∘ u))) =
    ∑ q : AdicCompletion.IdealBranch
        ((point (endpointPolynomial k b)).asIdeal.map (algebraMap k[X] S)),
      let Q := branchPoint k[X] S (point (endpointPolynomial k b)) q
      dvrFracOrd (IsDiscreteValuationRing.exists_irreducible
        (Localization.AtPrime Q.asIdeal)).choose_spec (endpointParameter k E b) •
        milnorKNorm k (ResidueField (Localization.AtPrime Q.asIdeal)) n
          (milnorKTupleSymbol (Units.map
            ((IsLocalRing.residue (Localization.AtPrime Q.asIdeal)).comp
              (algebraMap S (Localization.AtPrime Q.asIdeal))).toMonoidHom ∘ u)) := by
  rw [← endpointWeightedResidueSum_eq_baseNormSum k S E a,
    ← endpointWeightedResidueSum_eq_baseNormSum k S E b]
  exact endpointWeightedResidueSum_eq_all k S E a b n u

end Stacks.Chow.DedekindResidue

attribute [colib_tag "COL-1006",
  colib_ref "aglib_milnor_4f65be4e"
    "KTheory/MilnorK/Dedekind/AffineEndpointBaseNorm.lean:98-114" "adaptation"
    "The full endpoint sum expressed with actual ground-field norms"]
  Stacks.Chow.DedekindResidue.endpointWeightedResidueSum_eq_baseNormSum

attribute [colib_tag "COL-1006",
  colib_ref "aglib_milnor_4f65be4e"
    "KTheory/MilnorK/Dedekind/AffineEndpointNormAllDegrees.lean:85-90" "adaptation"
    "The endpoint equality in all homogeneous degrees",
  colib_ref "aglib_milnor_4f65be4e"
    "KTheory/MilnorK/Dedekind/AffineEndpointBaseNorm.lean:98-114" "adaptation"
    "The termwise ground-field norm formula used to rewrite both sides"]
  Stacks.Chow.DedekindResidue.endpointBaseNormSum_eq_all
