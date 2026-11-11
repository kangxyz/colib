/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.NormalizedEndpointCycles
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.ResiduePointEvaluation
public import Colib.RingTheory.KTheory.MilnorK.Dedekind.AffineEndpointBaseNorm
public import StacksFrontier.AlgebraicGeometry.Scheme.FibreResidueField
public import StacksFrontier.RingTheory.Length.RingEquiv

/-!
# Actual PointNorm evaluations of normalized diagonal endpoints

The original polynomial fiber points index precisely the ideal branches in
the native endpoint sum. Their full stalk lengths are the corresponding
discrete-valuation orders. The residue isomorphisms carry the actual field
scalars and every original Laurent coordinate. The native endpoint norm
equality then applies to the graph endpoints in every weight.

Adapted from Motivic `a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Cohomology/Diagonal/NormalizedEndpointNorm.lean:29-121`,
`Motivic/Cohomology/WeightTwo/Endpoints/ResidueScalar.lean:35-157`, and
`RelativeCurve/MilnorK/AffineEndpointGeometry.lean:39-113` under
`Motivic/Aglib/AlgebraicGeometry`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow
open scoped Polynomial BigOperators nonZeroDivisors

universe u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalBoundarySupport

open _root_.AlgebraicGeometry.Scheme DiagonalFiniteCyclePushforward
open DiagonalFinitePointEvaluation DiagonalResiduePointEvaluation PolynomialEndpointFiber
open Stacks.Chow.DedekindResidue Stacks.Chow.PolynomialDedekindResidue
open IsDedekindDomain IsLocalRing

attribute [local instance] Classical.decEq

section Branches

variable (k : Type u) [Field k]

private abbrev endpointPrime (a : k) : HeightOneSpectrum k[X] :=
  PolynomialDedekindResidue.point (DedekindResidue.endpointPolynomial k a)

private theorem endpoint_point (a : k) (x : Spec (.of k)) :
    endpoint a x = (⟨(endpointPrime k a).asIdeal, inferInstance⟩ : PrimeSpectrum k[X]) := by
  have hx : x = (⊥ : PrimeSpectrum k) := Subsingleton.elim _ _
  subst x
  apply PrimeSpectrum.ext
  change RingHom.ker (Polynomial.evalRingHom a) = Ideal.span {Polynomial.X - Polynomial.C a}
  exact Polynomial.ker_evalRingHom a

variable (S : Type u) [CommRing S] [IsDedekindDomain S] [Algebra k[X] S]
  [Module.Finite k[X] S] [Module.IsTorsionFree k[X] S]

private abbrev polynomialMap : Spec (.of S) ⟶ Spec (.of k[X]) :=
  Spec.map (CommRingCat.ofHom (algebraMap k[X] S))

private abbrev endpointFiber (a : k) := fiber (polynomialMap k S) a

private abbrev endpointToField (a : k) : endpointFiber k S a ⟶ Spec (.of k) :=
  pullback.fst (endpoint a) (polynomialMap k S)

private abbrev ambientPoint (a : k) (x : endpointFiber k S a) : Spec (.of S) :=
  fiberInclusion (polynomialMap k S) a x

private abbrev endpointBranches (a : k) :=
  AdicCompletion.IdealBranch ((endpointPrime k a).asIdeal.map (algebraMap k[X] S))

private def pointToPrimeOver (a : k) (x : endpointFiber k S a) :
    (endpointPrime k a).asIdeal.primesOver S := by
  let y := ambientPoint k S a x
  have hp : (polynomialMap k S) y = endpoint a (endpointToField k S a x) := by
    have h := congrArg (fun m : endpointFiber k S a ⟶ Spec (.of k[X]) => m x)
      (pullback.condition (f := endpoint a) (g := polynomialMap k S)).symm
    simpa only [Scheme.Hom.comp_apply] using h
  rw [endpoint_point] at hp
  exact ⟨y.asIdeal, y.isPrime, ⟨(congrArg PrimeSpectrum.asIdeal hp).symm⟩⟩

omit [IsDedekindDomain S] [Module.Finite k[X] S] [Module.IsTorsionFree k[X] S] in
private theorem pointToPrimeOver_bijective (a : k) :
    Function.Bijective (pointToPrimeOver k S a) := by
  constructor
  · intro x y h
    apply (fiberInclusion (polynomialMap k S) a).isClosedEmbedding.injective
    exact PrimeSpectrum.ext (congrArg Subtype.val h)
  · intro Q
    let y : Spec (.of S) := ⟨Q.val, Q.property.1⟩
    have hy : y ∈ Set.range (fiberInclusion (polynomialMap k S) a) := by
      change y ∈ Set.range (pullback.snd (endpoint a) (polynomialMap k S))
      rw [Scheme.Pullback.range_snd]
      refine ⟨genericPoint (Spec (.of k)), ?_⟩
      rw [endpoint_point]
      exact PrimeSpectrum.ext Q.property.2.over
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext (congrArg PrimeSpectrum.asIdeal hx)⟩

private def endpointBranchEquiv (a : k) : endpointFiber k S a ≃ endpointBranches k S a :=
  (Equiv.ofBijective (pointToPrimeOver k S a) (pointToPrimeOver_bijective k S a)).trans
    (Localization.primesOverEquivIdealBranch (endpointPrime k a).asIdeal (endpointPrime k a).ne_bot)

private abbrev endpointBranchPoint (a : k) (x : endpointFiber k S a) : HeightOneSpectrum S :=
  branchPoint k[X] S (endpointPrime k a) (endpointBranchEquiv k S a x)

private abbrev endpointLocalRing (a : k) (x : endpointFiber k S a) :=
  Localization.AtPrime (endpointBranchPoint k S a x).asIdeal

private def endpointRestriction (a : k) : S →+* Γ(endpointFiber k S a, ⊤) :=
  (fiberInclusion (polynomialMap k S) a).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom

private def endpointBranchResidueEquiv (a : k) (x : endpointFiber k S a) :
    ResidueField (endpointLocalRing k S a x) ≃+* (endpointFiber k S a).residueField x := by
  let y := ambientPoint k S a x
  let j := fiberInclusion (polynomialMap k S) a
  let e := (Scheme.Spec.residueFieldIso (.of S) y).symm.commRingCatIsoToRingEquiv
  let d := RingEquiv.ofBijective (j.residueFieldMap x).hom
    ⟨(j.residueFieldMap x).hom.injective,
      AlgebraicGeometry.surjective_residueFieldMap_of_surjectiveOnStalks j x⟩
  exact e.trans d

omit [Module.Finite k[X] S] in
private theorem endpointBranchResidueEquiv_eval (a : k) (x : endpointFiber k S a) (s : S) :
    endpointBranchResidueEquiv k S a x
        (residue (endpointLocalRing k S a x) (algebraMap S _ s)) =
      (endpointFiber k S a).Γevaluation x (endpointRestriction k S a s) := by
  let y := ambientPoint k S a x
  let j := fiberInclusion (polynomialMap k S) a
  have h := ConcreteCategory.congr_hom (Scheme.Spec.algebraMap_residueFieldIso_inv (.of S) y) s
  change (Scheme.Spec.residueFieldIso (.of S) y).inv
      (residue (Localization.AtPrime y.asIdeal) (algebraMap S _ s)) =
    (Spec (.of S)).Γevaluation y ((Scheme.ΓSpecIso (.of S)).inv s) at h
  change j.residueFieldMap x ((Scheme.Spec.residueFieldIso (.of S) y).inv
    (residue (Localization.AtPrime y.asIdeal) (algebraMap S _ s))) = _
  rw [h, Scheme.Γevaluation_naturality_apply]
  rfl

omit [IsDedekindDomain S] [Module.IsTorsionFree k[X] S] in
private theorem polynomialMapFinite : IsFinite (polynomialMap k S) :=
  (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

attribute [local instance] polynomialMapFinite

omit [IsDedekindDomain S] [Module.IsTorsionFree k[X] S] in
private theorem endpointToFieldFinite (a : k) : IsFinite (endpointToField k S a) := by
  change IsFinite (pullback.fst (endpoint a) (polynomialMap k S))
  infer_instance

omit [IsDedekindDomain S] [Module.IsTorsionFree k[X] S] in
private theorem endpointFiberNoetherian (a : k) : IsNoetherian (endpointFiber k S a) :=
  fiber_isNoetherian (polynomialMap k S) a

attribute [local instance] endpointToFieldFinite endpointFiberNoetherian

variable [Algebra k S] [IsScalarTower k k[X] S]

omit [IsDedekindDomain S] [Module.Finite k[X] S] [Module.IsTorsionFree k[X] S] in
private theorem endpointToField_eq (a : k) :
    endpointToField k S a = fiberInclusion (polynomialMap k S) a ≫
      Spec.map (CommRingCat.ofHom (algebraMap k S)) := by
  have he : endpoint a ≫ polynomialToField k = 𝟙 (Spec (.of k)) := by
    rw [← evaluationPoint_chart, Category.assoc, sourceChart1_polynomialToField]
    exact MorphismProperty.Over.w (evaluationPoint k a)
  have hp : polynomialMap k S ≫ polynomialToField k =
      Spec.map (CommRingCat.ofHom (algebraMap k S)) := by
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact (IsScalarTower.algebraMap_eq k k[X] S).symm
  have h := congrArg (fun f => f ≫ polynomialToField k)
    (pullback.condition (f := endpoint a) (g := polynomialMap k S))
  simpa only [Category.assoc, he, Category.comp_id, hp] using h

omit [IsDedekindDomain S] [Module.Finite k[X] S] [Module.IsTorsionFree k[X] S] in
private theorem endpointResidueScalar_eval (a : k) (x : endpointFiber k S a) (r : k) :
    residueScalar (endpointToField k S a) x r =
      (endpointFiber k S a).Γevaluation x (endpointRestriction k S a (algebraMap k S r)) := by
  unfold residueScalar
  rw [endpointToField_eq, Scheme.Hom.comp_appTop]
  have h := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k S))) r
  exact congrArg (fun t => (endpointFiber k S a).Γevaluation x
    ((fiberInclusion (polynomialMap k S) a).appTop t)) h.symm

private def endpointUnits {n : ℕ} (a : k) (u : Fin n → Sˣ) :
    Fin n → Γ(endpointFiber k S a, ⊤)ˣ :=
  Units.map (endpointRestriction k S a).toMonoidHom ∘ u

local instance endpointFiniteType : Algebra.FiniteType k S := Algebra.FiniteType.trans (S := k[X])
  (inferInstanceAs (Algebra.FiniteType k k[X])) (inferInstanceAs (Algebra.FiniteType k[X] S))

private theorem endpointLocalResidueFinite (a : k) (x : endpointFiber k S a) :
    FiniteDimensional k (ResidueField (endpointLocalRing k S a x)) :=
  Localization.finiteType_localResidue_finite k S (endpointBranchPoint k S a x).asIdeal

attribute [local instance] endpointLocalResidueFinite

variable [CharZero k]

private theorem residueValue_eq_branchNorm (a : k) (x : endpointFiber k S a) (n : ℕ)
    (u : Fin n → Sˣ) :
    residueValue (endpointToField k S a) (endpointUnits k S a u) x =
      milnorKNorm k (ResidueField (endpointLocalRing k S a x)) n
        (milnorKTupleSymbol (Units.map
          ((residue (endpointLocalRing k S a x)).comp
            (algebraMap S (endpointLocalRing k S a x))).toMonoidHom ∘ u)) := by
  let : Algebra k ((endpointFiber k S a).residueField x) :=
    residueAlgebra (endpointToField k S a) x
  let : Module.Finite k ((endpointFiber k S a).residueField x) :=
    residueFinite (endpointToField k S a) x
  let R := endpointLocalRing k S a x
  let L := ResidueField R
  let L' := (endpointFiber k S a).residueField x
  let : FiniteDimensional k L := endpointLocalResidueFinite k S a x
  let e := endpointBranchResidueEquiv k S a x
  let v : Fin n → Lˣ := Units.map ((residue R).comp (algebraMap S R)).toMonoidHom ∘ u
  have he : e.toRingHom.comp (algebraMap k L) =
      (algebraMap k L').comp (RingEquiv.refl k).toRingHom := by
    ext r
    change e (residue R (algebraMap S R (algebraMap k S r))) =
      residueScalar (endpointToField k S a) x r
    rw [endpointResidueScalar_eval]
    exact endpointBranchResidueEquiv_eval k S a x (algebraMap k S r)
  have h := milnorKNorm_map_ringEquiv (RingEquiv.refl k) e he n (milnorKTupleSymbol v)
  have hid : (RingEquiv.refl k).toRingHom = RingHom.id k := rfl
  rw [hid, milnorKTransport_id_apply, milnorKTransport_tupleSymbol] at h
  have hv : Units.map e.toRingHom.toMonoidHom ∘ v =
      fun i => Units.map ((endpointFiber k S a).Γevaluation x).hom.toMonoidHom
        (endpointUnits k S a u i) := by
    funext i
    apply Units.ext
    exact endpointBranchResidueEquiv_eval k S a x (u i).val
  rw [hv] at h
  exact h.symm

variable (K : Type u) [Field K] [Algebra S K] [IsFractionRing S K]
  [Algebra k[X] K] [IsScalarTower k[X] S K]
  [Algebra (RatFunc k) K] [IsScalarTower k[X] (RatFunc k) K]

omit [CharZero k] [Algebra k S] [IsScalarTower k k[X] S] in
private theorem endpointCoefficient_eq_order (a : k) (x : endpointFiber k S a) :
    AlgebraicCycle.fundamentalCycle (endpointFiber k S a) x =
      dvrFracOrd (IsDiscreteValuationRing.exists_irreducible
        (endpointLocalRing k S a x)).choose_spec (endpointParameter k K a) := by
  let j := fiberInclusion (polynomialMap k S) a
  let y := ambientPoint k S a x
  let R := endpointLocalRing k S a x
  let t := algebraMap k[X] S (Polynomial.X - Polynomial.C a)
  let s := algebraMap S R t
  let hπ := (IsDiscreteValuationRing.exists_irreducible R).choose_spec
  have hx : x ∈ genericPoints (endpointFiber k S a) := by
    apply mem_genericPoints_of_isFinite_image (endpointToField k S a)
    rw [genericPoints_eq_singleton, Set.mem_singleton_iff]
    exact Subsingleton.elim _ _
  have hmap : algebraMap R K s = (endpointParameter k K a : K) := by
    change algebraMap R K (algebraMap S R (algebraMap k[X] S (Polynomial.X - Polynomial.C a))) =
      algebraMap (RatFunc k) K (algebraMap k[X] (RatFunc k) (Polynomial.X - Polynomial.C a))
    rw [← IsScalarTower.algebraMap_apply S R K, ← IsScalarTower.algebraMap_apply k[X] S K,
      ← IsScalarTower.algebraMap_apply k[X] (RatFunc k) K]
  have hs : s ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hmap
    exact (endpointParameter k K a).ne_zero hmap.symm
  obtain ⟨m, v, hm⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs hπ
  have horder : dvrFracOrd hπ (endpointParameter k K a) = (m : ℤ) := by
    apply dvrFracOrd_eq_of_eq (u := v) hπ
    rw [← hmap, hm, map_mul, map_pow, zpow_natCast]
  let e := (AlgebraicGeometry.Spec.stalkIso (.of S) y).commRingCatIsoToRingEquiv
  let germ := (Spec (.of S)).presheaf.germ ⊤ y trivial (equation (polynomialMap k S) a)
  have heq : equation (polynomialMap k S) a = (Scheme.ΓSpecIso (.of S)).inv t :=
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (algebraMap k[X] S))) (Polynomial.X - Polynomial.C a)).symm
  have he : e germ = s := by
    have h := ConcreteCategory.congr_hom
      (AlgebraicGeometry.Spec.germ_stalkMapIso_hom (R := CommRingCat.of S) y)
      (equation (polynomialMap k S) a)
    change e germ = algebraMap S R ((Scheme.ΓSpecIso (.of S)).hom
      (equation (polynomialMap k S) a)) at h
    have hid : (Scheme.ΓSpecIso (.of S)).hom ((Scheme.ΓSpecIso (.of S)).inv t) = t :=
      (Scheme.ΓSpecIso (.of S)).commRingCatIsoToRingEquiv.apply_symm_apply t
    rw [heq, hid] at h
    exact h
  have hl := Module.quotient_length_eq_of_ringEquiv e (Ideal.span {germ})
  rw [Ideal.map_span, Set.image_singleton] at hl
  change _ = Module.length R (R ⧸ Ideal.span {e germ}) at hl
  rw [he] at hl
  rw [AlgebraicCycle.fundamentalCycle_apply_generic _ ⟨x, hx⟩,
    ← closedImmersionQuotientStalkLength_image j x]
  unfold closedImmersionQuotientStalkLength
  rw [fiberInclusion_ker_stalk]
  change ((Module.length _ (_ ⧸ Ideal.span {germ})).toNat : ℤ) =
    dvrFracOrd hπ (endpointParameter k K a)
  rw [hl]
  change ((Ring.ord R s).toNat : ℤ) = dvrFracOrd hπ (endpointParameter k K a)
  rw [hm, ord_unit_mul_pow hπ, ENat.toNat_natCast, horder]

private theorem residue_sum_eq_endpoint (a : k) (n : ℕ) (u : Fin n → Sˣ) :
    letI := finiteSchemeFintype (endpointToField k S a)
    (∑ x : endpointFiber k S a, AlgebraicCycle.fundamentalCycle (endpointFiber k S a) x •
      residueValue (endpointToField k S a) (endpointUnits k S a u) x) =
      endpointWeightedResidueSum k S K a n u := by
  let : Fintype (endpointFiber k S a) := finiteSchemeFintype (endpointToField k S a)
  rw [endpointWeightedResidueSum_eq_baseNormSum]
  rw [← (endpointBranchEquiv k S a).sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  rw [endpointCoefficient_eq_order k S K a x, residueValue_eq_branchNorm k S a x n u]

end Branches

variable {k : Type u} [Field k] [CharZero k] {q : ℕ} (Z : Generator k q)

omit [CharZero k] in
private theorem normalizedFiberInclusion_coordinate (a : k) (i : Fin q) :
    schemeCoordinateUnit (normalizedFiberInclusion Z a) i =
      Units.map (normalizedFiberScalar Z a).toMonoidHom (normalizedCoordinateUnit Z i) := by
  apply Units.ext
  change (normalizedFiberInclusion Z a ≫ ambientCoordinate k q i).appTop
    (multiplicativeGroupBaseChangeCoordinate (Spec (.of k))).val = _
  have h : normalizedFiberInclusion Z a ≫ ambientCoordinate k q i =
      fiberInclusion (normalizationBaseMap Z) a ≫ normalizationMap Z ≫
        (targetProjection Z ≫ (SmoothSite.torusCoordinate (Spec (.of k)) q i).left) := by
    change normalizedFiberInclusion Z a ≫
      pullback.snd (SmoothSite.base (Spec (.of k))).hom (target k q).hom ≫
        (SmoothSite.torusCoordinate (Spec (.of k)) q i).left = _
    exact normalizedFiberInclusion_snd_assoc Z a _
  rw [h, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, normalizationMap_appTop]
  rfl

/-- The native endpoint sum uses the original normalized ring and original coordinate units. -/
def normalizedEndpointValue (a : k) : MilnorKTheory k q :=
  endpointWeightedResidueSum k (normalizationRing Z) (FractionRing (coordinateRing Z)) a q
    (normalizedCoordinateUnit Z)

/-- The native endpoint sum is independent of the point of the original affine parameter. -/
theorem normalizedEndpointValue_eq (a b : k) :
    normalizedEndpointValue Z a = normalizedEndpointValue Z b :=
  endpointWeightedResidueSum_eq_all k (normalizationRing Z)
    (FractionRing (coordinateRing Z)) a b q (normalizedCoordinateUnit Z)

/-- Each actual graph endpoint evaluates to the full native normalized residue sum. -/
theorem cycleValue_endpoint_normalized (a : k) :
    DiagonalPointNorm.cycleValue k q
      ((Cor.graphFunctor k).map (evaluationPoint k a) ≫
        singleFiniteCorrespondence (source k 1).hom (target k q).hom Z.val Z.property 1) =
      normalizedEndpointValue Z a := by
  let S := normalizationRing Z
  let : Algebra k S := ((algebraMap k[X] S).comp (algebraMap k k[X])).toAlgebra
  let : IsScalarTower k k[X] S := IsScalarTower.of_algebraMap_eq' rfl
  have h := cycleValue_eq_residue_sum_of_finite (normalizedFiberBase Z a)
    (normalizedFiberInclusion Z a) (normalizedFiberInclusion_fst Z a)
    (fun i => Units.map (normalizedFiberScalar Z a).toMonoidHom (normalizedCoordinateUnit Z i))
    (normalizedFiberInclusion_coordinate Z a)
    ((Cor.graphFunctor k).map (evaluationPoint k a) ≫
      singleFiniteCorrespondence (source k 1).hom (target k q).hom Z.val Z.property 1)
    (graphEndpoint_val_eq_normalized Z a)
  exact h.trans (residue_sum_eq_endpoint k S (FractionRing (coordinateRing Z)) a q
    (normalizedCoordinateUnit Z))

/-- The original two endpoint evaluations agree on every native signed one-chain. -/
theorem cycleValue_endpoint_eq
    (α : Cor.mk (source k 1) ⟶ Cor.mk (target k q)) :
    DiagonalPointNorm.cycleValue k q ((Cor.graphFunctor k).map (evaluationPoint k (0 : k)) ≫ α) =
      DiagonalPointNorm.cycleValue k q
        ((Cor.graphFunctor k).map (evaluationPoint k (1 : k)) ≫ α) := by
  let T := Cor.mk (target k q)
  let d₀ := (Cor.graphFunctor k).map (evaluationPoint k (0 : k))
  let d₁ := (Cor.graphFunctor k).map (evaluationPoint k (1 : k))
  have h : (DiagonalPointNorm.cycleValue k q).comp (Preadditive.leftComp T d₀) =
      (DiagonalPointNorm.cycleValue k q).comp (Preadditive.leftComp T d₁) := by
    apply finiteCorrespondences.addHom_ext_one (source k 1).hom (target k q).hom
    intro z hz
    let Z : Generator k q := ⟨z, hz⟩
    change DiagonalPointNorm.cycleValue k q ((Cor.graphFunctor k).map (evaluationPoint k (0 : k)) ≫
        singleFiniteCorrespondence (source k 1).hom (target k q).hom Z.val Z.property 1) =
      DiagonalPointNorm.cycleValue k q ((Cor.graphFunctor k).map (evaluationPoint k (1 : k)) ≫
        singleFiniteCorrespondence (source k 1).hom (target k q).hom Z.val Z.property 1)
    rw [cycleValue_endpoint_normalized Z 0, cycleValue_endpoint_normalized Z 1]
    exact normalizedEndpointValue_eq Z 0 1
  exact DFunLike.congr_fun h α

end AlgebraicGeometry.MotivicCohomology.DiagonalBoundarySupport
