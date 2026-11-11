/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.FieldTheory.IntermediateField.CompositumImage
public import Colib.RingTheory.AdjoinRoot.TowerFactorPullback
public import Colib.RingTheory.KTheory.MilnorK.Norm.PrimeChosenPresentation
public import Colib.RingTheory.KTheory.MilnorK.Norm.PresentationSupport
public import Colib.RingTheory.KTheory.MilnorK.Norm.PrimeTowerPure
public import Colib.RingTheory.KTheory.MilnorK.Norm.PrimeTowerSeparable
public import Colib.FieldTheory.PurelyInseparable.PrimeDegree
public import Colib.FieldTheory.AdjoinRoot.SeparablePresentation
public import Colib.FieldTheory.PurelyInseparable.MinpolyBaseChange
public import Colib.RingTheory.KTheory.MilnorK.Norm.PurePrimeResidueEquiv
public import Colib.RingTheory.KTheory.MilnorK.Norm.NormalPrimeScalarBaseChange

/-!
# Native prime coherence inputs for the chosen-norm induction

These propositions state the exact field-coordinate consequences needed from
the polynomial prime tower and diamond. Their arguments retain the literal
simple norm, the actual prime subfield and the actual compositum inside the
original common field. The prime-tower and pure-prime-diamond arguments below
supply the inputs used by the pure induction. The general normal-diamond
proposition is retained separately for the broader normal-ambient route.
-/

@[expose] public noncomputable section

open Polynomial Module IntermediateField

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

local instance primeCoherence_nativeIrreducible {K : Type u} [Field K]
    {d : ℕ} (q : MonicIrreducibleOfDegree K d) : Fact (Irreducible (poly q)) :=
  ⟨irreducible q⟩

local instance primeCoherence_rootFinite {K : Type u} [Field K]
    {d : ℕ} (q : MonicIrreducibleOfDegree K d) : Module.Finite K (AdjoinRoot (poly q)) :=
  (monic q).finite_adjoinRoot

/-- An actual normal prime lower field supplies a relative presentation of a
polynomial-presented top field in which its original simple norm factors. -/
def NativePrimeSimpleNormFactorization (p : ℕ) : Prop :=
  ∀ (K P L : Type u) [Field K] [Field P] [Field L]
    [Algebra K P] [Algebra P L] [Algebra K L] [IsScalarTower K P L]
    [FiniteDimensional K P] [FiniteDimensional K L] [Normal K P]
    (_hP : finrank K P = p) {d : ℕ} (q : MonicIrreducibleOfDegree K d)
    (g : L ≃ₐ[K] AdjoinRoot (poly q)),
    ∃ (e : ℕ) (r : MonicIrreducibleOfDegree P e) (f : L ≃ₐ[P] AdjoinRoot (poly r)),
      ∀ x : MilnorKRing L,
        simpleMilnorNorm q (milnorKRingMap g.toRingHom x) =
          milnorKNormRing K P (simpleMilnorNorm r (milnorKRingMap f.toRingHom x))

/-- The actual chosen norms of two normal prime fields commute around their
actual compositum. Relative degree-one branches are included in this statement. -/
def NativePrimeNormDiamond (p : ℕ) : Prop :=
  ∀ (K P Q L : Type u) [Field K] [Field P] [Field Q] [Field L]
    [Algebra K P] [Algebra K Q] [Algebra K L] [Algebra P L] [Algebra Q L]
    [IsScalarTower K P L] [IsScalarTower K Q L]
    [FiniteDimensional K P] [FiniteDimensional K Q] [FiniteDimensional K L]
    [Normal K P] [Normal K Q]
    (_hP : finrank K P = p) (_hQ : finrank K Q = p),
    let C := IntermediateField.adjoin P (Set.range (algebraMap Q L))
    let _ : Algebra Q C := (adjoinRangeFactor Q P L).toAlgebra
    let _ : IsScalarTower Q C L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let _ : FiniteDimensional P C :=
      finiteDimensional_adjoin_range_of_finiteDimensional K Q P L
    let _ : FiniteDimensional Q L := FiniteDimensional.right K Q L
    let _ : FiniteDimensional Q C := FiniteDimensional.left Q C L
    ∀ x : MilnorKRing C,
      milnorKNormRing K P (milnorKNormRing P C x) =
        milnorKNormRing K Q (milnorKNormRing Q C x)

/-- The prime diamond needed by the pure induction requires only two purely
inseparable prime fields, independently of mixed prime rectangles. -/
def NativePurePrimeNormDiamond (p : ℕ) : Prop :=
  ∀ (K P Q L : Type u) [Field K] [Field P] [Field Q] [Field L]
    [Algebra K P] [Algebra K Q] [Algebra K L] [Algebra P L] [Algebra Q L]
    [IsScalarTower K P L] [IsScalarTower K Q L]
    [FiniteDimensional K P] [FiniteDimensional K Q] [FiniteDimensional K L]
    [IsPurelyInseparable K P] [IsPurelyInseparable K Q]
    (_hP : finrank K P = p) (_hQ : finrank K Q = p),
    let C := IntermediateField.adjoin P (Set.range (algebraMap Q L))
    let _ : Algebra Q C := (adjoinRangeFactor Q P L).toAlgebra
    let _ : IsScalarTower Q C L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let _ : FiniteDimensional P C :=
      finiteDimensional_adjoin_range_of_finiteDimensional K Q P L
    let _ : FiniteDimensional Q L := FiniteDimensional.right K Q L
    let _ : FiniteDimensional Q C := FiniteDimensional.left Q C L
    ∀ x : MilnorKRing C,
      milnorKNormRing K P (milnorKNormRing P C x) =
        milnorKNormRing K Q (milnorKNormRing Q C x)

private theorem primeCoherence_simple_tower
    {K : Type u} [Field K] {d e : ℕ}
    (p : MonicIrreducibleOfDegree K d) (hp : d.Prime)
    [Normal K (AdjoinRoot (poly p))]
    (h : MonicIrreducibleOfDegree K e)
    (f : AdjoinRoot (poly p) →ₐ[K] AdjoinRoot (poly h))
    (x : MilnorKRing (AdjoinRoot (poly h))) :
    simpleMilnorNorm h x =
      simpleMilnorNorm p
        (simpleMilnorNorm (AdjoinRoot.towerFactor (poly p) (poly h) f).1.2
          (milnorKRingMap
            (AdjoinRoot.map (algebraMap K (AdjoinRoot (poly p))) (poly h)
              (poly (AdjoinRoot.towerFactor (poly p) (poly h) f).1.2)
              (AdjoinRoot.towerFactor (poly p) (poly h) f).2) x)) := by
  let : FiniteDimensional K (AdjoinRoot (poly p)) := (monic p).finite_adjoinRoot
  by_cases hs : Algebra.IsSeparable K (AdjoinRoot (poly p))
  · let : Algebra.IsSeparable K (AdjoinRoot (poly p)) := hs
    have hsep := AdjoinRoot.polynomial_separable_of_algHom
      (poly p) (monic p) (AlgHom.id K (AdjoinRoot (poly p)))
    exact simpleMilnorNorm_eq_prime_tower_of_separable p hsep hp h f x
  · have hp' : Nat.Prime (finrank K (AdjoinRoot (poly p))) := by
      rw [(AdjoinRoot.powerBasis (ne_zero p)).finrank, AdjoinRoot.powerBasis_dim,
        natDegree_eq]
      exact hp
    let : IsPurelyInseparable K (AdjoinRoot (poly p)) :=
      isPurelyInseparable_of_finrank_prime_of_not_isSeparable hp' hs
    exact simpleMilnorNorm_eq_prime_tower_of_isPurelyInseparable p hp h f x

/-- The actual polynomial prime towers supply the native relative-presentation
input. The lower chosen norm uses its own selected presentation throughout. -/
theorem nativePrimeSimpleNormFactorization (p : ℕ) [Fact p.Prime] :
    NativePrimeSimpleNormFactorization.{u} p := by
  intro K P L _ _ _ _ _ _ _ _ _ _ hP d q g
  classical
  have hp : Nat.Prime (finrank K P) := hP.symm ▸ (Fact.out : p.Prime)
  obtain ⟨a, _ha, ε₀, hdegree, hchosen⟩ :=
    exists_selected_simpleMilnorNorm_presentation_of_prime hp
  let p₀ := minpolyOfDegree K (Algebra.IsIntegral.isIntegral (R := K) a)
  let ε : P ≃ₐ[K] AdjoinRoot (poly p₀) :=
    { toRingEquiv := ε₀.toRingEquiv
      commutes' := ε₀.commutes }
  let : Normal K (AdjoinRoot (poly p₀)) := Normal.of_algEquiv ε
  have hp₀ : (minpoly K a).natDegree.Prime := hdegree.symm ▸ hp
  let i := g.toAlgHom.comp ((IsScalarTower.toAlgHom K P L).comp ε.symm.toAlgHom)
  let q₀ := AdjoinRoot.towerFactor (poly p₀) (poly q) i
  obtain ⟨r, f, hr, _hpoly, hmap⟩ :=
    AdjoinRoot.exists_towerFactor_pullback_presentation p₀ q ε g
  refine ⟨q₀.1.1, r, f, ?_⟩
  intro x
  have hnorm := simpleMilnorNorm_map_of_poly_eq_map
    ε.toRingHom r q₀.1.2 hr (milnorKRingMap f.toRingHom x)
  have houter := congrArg (simpleMilnorNorm p₀) hnorm
  have hleft := milnorKRingMap_comp_apply f.toRingHom
    (AdjoinRoot.map ε.toRingHom (poly r) (poly q₀.1.2) (hr ▸ dvd_rfl)) x
  have hsquare := congrArg
    (fun ψ : L →+* AdjoinRoot (poly q₀.1.2) => milnorKRingMap ψ x) hmap
  have hright := milnorKRingMap_comp_apply g.toRingHom
    (AdjoinRoot.map (algebraMap K (AdjoinRoot (poly p₀)))
      (poly q) (poly q₀.1.2) q₀.2) x
  have hmaps := hleft.trans (hsquare.trans hright.symm)
  have hmiddle := congrArg (simpleMilnorNorm p₀)
    (congrArg (simpleMilnorNorm q₀.1.2) hmaps)
  have htower := primeCoherence_simple_tower p₀ hp₀ q i (milnorKRingMap g.toRingHom x)
  have hsimple := houter.trans (hmiddle.trans htower.symm)
  have hselected := hchosen (simpleMilnorNorm r (milnorKRingMap f.toRingHom x))
  change milnorKNormRing K P (simpleMilnorNorm r (milnorKRingMap f.toRingHom x)) =
    simpleMilnorNorm p₀
      (milnorKRingMap ε.toRingHom (simpleMilnorNorm r (milnorKRingMap f.toRingHom x)))
    at hselected
  exact hsimple.symm.trans hselected.symm

private theorem primeCoherence_surjective_of_adjoin_range_eq_top
    {A B D Q : Type u} [Field A] [Field B] [Field D] [Field Q]
    [Algebra A D] [Algebra B D] (f : Q →+* D)
    (hA : ∀ a : A, algebraMap A D a ∈ f.fieldRange)
    (hB : ∀ b : B, algebraMap B D b ∈ f.fieldRange)
    (hgen : adjoin A (Set.range (algebraMap B D)) = ⊤) : Function.Surjective f := by
  let C : IntermediateField A D := f.fieldRange.toIntermediateField hA
  have hle : adjoin A (Set.range (algebraMap B D)) ≤ C := by
    apply adjoin_le_iff.mpr
    rintro _ ⟨b, rfl⟩
    exact hB b
  have htop : (⊤ : IntermediateField A D) ≤ C := hgen ▸ hle
  intro x
  have hx : x ∈ (⊤ : IntermediateField A D) := IntermediateField.mem_top
  exact RingHom.mem_fieldRange.mp (htop hx)

private theorem primeCoherence_isPurelyInseparable_of_adjoin_range_eq_top
    {K A B D : Type u} [Field K] [Field A] [Field B] [Field D]
    [Algebra K A] [Algebra K B] [Algebra K D] [Algebra A D] [Algebra B D]
    [IsScalarTower K A D] [IsScalarTower K B D] [IsPurelyInseparable K B]
    (hgen : adjoin A (Set.range (algebraMap B D)) = ⊤) : IsPurelyInseparable A D := by
  obtain ⟨q, _⟩ := ExpChar.exists K
  let : ExpChar A q := expChar_of_injective_algebraMap (algebraMap K A).injective q
  apply isPurelyInseparable_iff_perfectClosure_eq_top.mpr
  apply top_unique
  rw [← hgen, adjoin_le_iff]
  rintro _ ⟨b, rfl⟩
  obtain ⟨n, c, hc⟩ := IsPurelyInseparable.pow_mem K q b
  refine (mem_perfectClosure_iff_pow_mem q).mpr ⟨n, algebraMap K A c, ?_⟩
  rw [← IsScalarTower.algebraMap_apply K A D, IsScalarTower.algebraMap_apply K B D,
    hc, map_pow]

private theorem primeCoherence_adjoin_range_swap
    {A B D : Type u} [Field A] [Field B] [Field D] [Algebra A D] [Algebra B D]
    (hgen : adjoin A (Set.range (algebraMap B D)) = ⊤) :
    adjoin B (Set.range (algebraMap A D)) = ⊤ := by
  let C := adjoin B (Set.range (algebraMap A D))
  have hA (a : A) : algebraMap A D a ∈ C :=
    IntermediateField.subset_adjoin B _ ⟨a, rfl⟩
  let C' : IntermediateField A D := C.toSubfield.toIntermediateField hA
  have hle : adjoin A (Set.range (algebraMap B D)) ≤ C' := by
    apply adjoin_le_iff.mpr
    rintro _ ⟨b, rfl⟩
    exact C.algebraMap_mem b
  have htop : (⊤ : IntermediateField A D) ≤ C' := hgen ▸ hle
  apply top_unique
  intro x _
  exact htop (IntermediateField.mem_top : x ∈ (⊤ : IntermediateField A D))

private theorem primeCoherence_norm_eq_simple_of_pure_dvd
    {F : Type u} [Field F] {d ell : ℕ} (q : MonicIrreducibleOfDegree F d)
    [IsPurelyInseparable F (AdjoinRoot (poly q))]
    (hp : ell.Prime) (hdiv : finrank F (AdjoinRoot (poly q)) ∣ ell)
    (x : MilnorKRing (AdjoinRoot (poly q))) :
    milnorKNormRing F (AdjoinRoot (poly q)) x = simpleMilnorNorm q x := by
  let f : AdjoinRoot (poly q) ≃ₐ[F] (F[X] ⧸ Ideal.span {poly q}) :=
    { toRingEquiv := RingEquiv.refl _, commutes' := fun _ => rfl }
  have hfin : finrank F (AdjoinRoot (poly q)) = d := by
    rw [(AdjoinRoot.powerBasis (ne_zero q)).finrank, AdjoinRoot.powerBasis_dim,
      natDegree_eq]
  have hf : milnorKRingMap f.toRingHom x = x := milnorKRingMap_id_apply x
  rcases (Nat.dvd_prime hp).mp hdiv with h1 | hprime
  · exact (milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_degree_one
      q (hfin.symm.trans h1) f x).trans (congrArg (simpleMilnorNorm q) hf)
  · exact (milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_prime_of_isPurelyInseparable
      (hprime.symm ▸ hp) q f x).trans (congrArg (simpleMilnorNorm q) hf)

section PurePairCoordinates

variable {K A B D : Type u} [Field K] [Field A] [Field B] [Field D]
  [Algebra K A] [Algebra K B] [Algebra K D] [Algebra A D] [Algebra B D]
  [IsScalarTower K A D] [IsScalarTower K B D]
  {d e : ℕ} (p : MonicIrreducibleOfDegree K d) (h : MonicIrreducibleOfDegree K e)
  (q : {q : Σ f : ℕ, MonicIrreducibleOfDegree (AdjoinRoot (poly p)) f //
    poly q.2 ∣ (poly h).map (algebraMap K (AdjoinRoot (poly p)))})

local notation "PairE" => AdjoinRoot (poly p)
local notation "PairH" => AdjoinRoot (poly h)
local notation "PairQ" => AdjoinRoot (poly (Sigma.snd (Subtype.val q)))
local notation "pairMap" => AdjoinRoot.map (algebraMap K PairE) (poly h)
  (poly (Sigma.snd (Subtype.val q))) (Subtype.property q)

private theorem exists_primePurePair_quotientEquiv
    (eB : B ≃ₐ[K] PairE) (eA : A ≃ₐ[K] PairH)
    (hroot : (poly q.1.2).eval₂ ((algebraMap B D).comp eB.symm.toRingHom)
      (algebraMap A D (eA.symm (AdjoinRoot.root (poly h)))) = 0)
    (hgen : adjoin A (Set.range (algebraMap B D)) = ⊤) :
    ∃ τ : D ≃+* PairQ,
      τ.toRingHom.comp (algebraMap B D) = (algebraMap PairE PairQ).comp eB.toRingHom ∧
      τ.toRingHom.comp (algebraMap A D) = RingHom.comp pairMap eA.toRingHom := by
  let j : PairE →+* D := (algebraMap B D).comp eB.symm.toRingHom
  let jA : PairH →ₐ[K] D := (IsScalarTower.toAlgHom K A D).comp eA.symm.toAlgHom
  have hj : j.comp (algebraMap K PairE) = algebraMap K D := by
    apply RingHom.ext
    intro a
    change algebraMap B D (eB.symm (algebraMap K PairE a)) = algebraMap K D a
    rw [eB.symm.commutes, ← IsScalarTower.algebraMap_apply K B D]
  have hrootQ : (poly q.1.2).eval₂ j (jA (AdjoinRoot.root (poly h))) = 0 := hroot
  let ψ : PairQ →+* D := AdjoinRoot.lift j (jA (AdjoinRoot.root (poly h))) hrootQ
  have hψB (a : PairE) : ψ (algebraMap PairE PairQ a) = j a :=
    AdjoinRoot.lift_of hrootQ
  have hψA : ψ.comp pairMap = (algebraMap A D).comp eA.symm.toRingHom := by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro a
      change ψ (pairMap (AdjoinRoot.of (poly h) a)) =
        algebraMap A D (eA.symm (algebraMap K PairH a))
      rw [eA.symm.commutes, ← IsScalarTower.algebraMap_apply K A D]
      rw [AdjoinRoot.map_of]
      exact (hψB (algebraMap K PairE a)).trans (RingHom.congr_fun hj a)
    · change ψ (pairMap (AdjoinRoot.root (poly h))) = jA (AdjoinRoot.root (poly h))
      rw [AdjoinRoot.map_root]
      exact AdjoinRoot.lift_root hrootQ
  have hψsurj : Function.Surjective ψ := by
    refine primeCoherence_surjective_of_adjoin_range_eq_top ψ ?_ ?_ hgen
    · intro a
      exact ⟨pairMap (eA a), (RingHom.congr_fun hψA (eA a)).trans
        (congrArg (algebraMap A D) (eA.symm_apply_apply a))⟩
    · intro b
      exact ⟨algebraMap PairE PairQ (eB b), (hψB (eB b)).trans
        (congrArg (algebraMap B D) (eB.symm_apply_apply b))⟩
  let τ : D ≃+* PairQ := (RingEquiv.ofBijective ψ ⟨ψ.injective, hψsurj⟩).symm
  refine ⟨τ, ?_, ?_⟩
  · apply RingHom.ext
    intro b
    change τ (algebraMap B D b) = algebraMap PairE PairQ (eB b)
    apply τ.symm.injective
    rw [τ.symm_apply_apply]
    change algebraMap B D b = ψ (algebraMap PairE PairQ (eB b))
    rw [hψB]
    exact congrArg (algebraMap B D) (eB.symm_apply_apply b).symm
  · apply RingHom.ext
    intro a
    change τ (algebraMap A D a) = pairMap (eA a)
    apply τ.symm.injective
    rw [τ.symm_apply_apply]
    change algebraMap A D a = ψ (pairMap (eA a))
    exact ((RingHom.congr_fun hψA (eA a)).trans
      (congrArg (algebraMap A D) (eA.symm_apply_apply a))).symm

variable [FiniteDimensional K A] [FiniteDimensional K B] [FiniteDimensional A D]
  [FiniteDimensional B D] [IsPurelyInseparable K A] [IsPurelyInseparable K B]

omit [Algebra K D] [IsScalarTower K A D] [IsScalarTower K B D] in
private theorem primePurePair_of_quotientEquiv
    [IsPurelyInseparable A D] [IsPurelyInseparable B D]
    (ell : ℕ) (hPrime : ell.Prime) (hA : finrank K A = ell) (hB : finrank K B = ell)
    (hp₀ : d.Prime) (hdivBD : finrank B D ∣ ell) (hdivAD : finrank A D ∣ ell)
    (eB : B ≃ₐ[K] PairE) (eA : A ≃ₐ[K] PairH) (τ : D ≃+* PairQ)
    (hτB : τ.toRingHom.comp (algebraMap B D) = (algebraMap PairE PairQ).comp eB.toRingHom)
    (hτA : τ.toRingHom.comp (algebraMap A D) = RingHom.comp pairMap eA.toRingHom)
    (x : MilnorKRing D) :
    milnorKNormRing K B (milnorKNormRing B D x) =
      milnorKNormRing K A (milnorKNormRing A D x) := by
  let r := AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h) q
  let R := AdjoinRoot (poly r.1.2)
  let s : PairQ ≃+* R := AdjoinRoot.tensorSwapFactorQuotientEquiv (poly p) (poly h) q
  let υ : D ≃+* R := τ.trans s
  have hυA : υ.toRingHom.comp (algebraMap A D) = (algebraMap PairH R).comp eA.toRingHom := by
    apply RingHom.ext
    intro a
    change s (τ (algebraMap A D a)) = algebraMap PairH R (eA a)
    have heq : τ (algebraMap A D a) = pairMap (eA a) := RingHom.congr_fun hτA a
    rw [heq]
    exact AdjoinRoot.tensorSwapFactorQuotientEquiv_map (poly p) (poly h) q (eA a)
  let : IsPurelyInseparable K PairE := eB.isPurelyInseparable
  let : IsPurelyInseparable PairE PairQ := IsPurelyInseparable.of_equiv_equiv eB.toRingEquiv τ hτB
  let : IsPurelyInseparable PairH R := IsPurelyInseparable.of_equiv_equiv eA.toRingEquiv υ hυA
  have hdivEQ : finrank PairE PairQ ∣ ell :=
    Algebra.finrank_eq_of_equiv_equiv eB.toRingEquiv τ hτB.symm ▸ hdivBD
  have hdivHR : finrank PairH R ∣ ell :=
    Algebra.finrank_eq_of_equiv_equiv eA.toRingEquiv υ hυA.symm ▸ hdivAD
  let y : MilnorKRing PairQ := milnorKRingMap τ.toRingHom x
  let w : MilnorKRing R := milnorKRingMap υ.toRingHom x
  have hBnorm : milnorKRingMap eB.toRingHom (milnorKNormRing B D x) =
      milnorKNormRing PairE PairQ y :=
    milnorKNormRing_map_ringEquiv_of_isPurelyInseparable_of_dvd_prime
      hPrime hdivBD eB.toRingEquiv τ hτB x
  have hQnorm : milnorKNormRing PairE PairQ y = simpleMilnorNorm q.1.2 y :=
    primeCoherence_norm_eq_simple_of_pure_dvd q.1.2 hPrime hdivEQ y
  have hBcomparison :=
    milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_prime_of_isPurelyInseparable
      (hB.symm ▸ hPrime) p eB (milnorKNormRing B D x)
  have hleft : milnorKNormRing K B (milnorKNormRing B D x) =
      simpleMilnorNorm p (simpleMilnorNorm q.1.2 y) :=
    hBcomparison.trans (congrArg (simpleMilnorNorm p) (hBnorm.trans hQnorm))
  have hAnorm : milnorKRingMap eA.toRingHom (milnorKNormRing A D x) =
      milnorKNormRing PairH R w :=
    milnorKNormRing_map_ringEquiv_of_isPurelyInseparable_of_dvd_prime
      hPrime hdivAD eA.toRingEquiv υ hυA x
  have hRnorm : milnorKNormRing PairH R w = simpleMilnorNorm r.1.2 w :=
    primeCoherence_norm_eq_simple_of_pure_dvd r.1.2 hPrime hdivHR w
  have hright : milnorKNormRing K A (milnorKNormRing A D x) =
      simpleMilnorNorm h (simpleMilnorNorm r.1.2 w) :=
    (milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_prime_of_isPurelyInseparable
      (hA.symm ▸ hPrime) h eA (milnorKNormRing A D x)).trans
        (congrArg (simpleMilnorNorm h) (hAnorm.trans hRnorm))
  have hswap : milnorKRingMap s.toRingHom y = w :=
    milnorKRingMap_comp_apply τ.toRingHom s.toRingHom x
  have hdiamond := simpleMilnorNorm_prime_diamond_of_isPurelyInseparable p hp₀ h q y
  exact hleft.trans (hdiamond.trans
    ((congrArg (simpleMilnorNorm h) (congrArg (simpleMilnorNorm r.1.2) hswap)).trans hright.symm))

end PurePairCoordinates

/-- Two purely inseparable prime fields have the native chosen-norm diamond
around their actual compositum. The actual minpoly factor retains relative
degree one and prime degree; the argument cancels no Milnor-group scalar. -/
theorem milnorKNormRing_comp_of_isPurelyInseparable_prime_pair
    {K A B D : Type u} [Field K] [Field A] [Field B] [Field D]
    [Algebra K A] [Algebra K B] [Algebra K D] [Algebra A D] [Algebra B D]
    [IsScalarTower K A D] [IsScalarTower K B D]
    [FiniteDimensional K A] [FiniteDimensional K B]
    [FiniteDimensional A D] [FiniteDimensional B D]
    [IsPurelyInseparable K A] [IsPurelyInseparable K B]
    (ell : ℕ) (hPrime : ell.Prime) (hA : finrank K A = ell) (hB : finrank K B = ell)
    (hgen : adjoin A (Set.range (algebraMap B D)) = ⊤) (x : MilnorKRing D) :
    milnorKNormRing K B (milnorKNormRing B D x) =
      milnorKNormRing K A (milnorKNormRing A D x) := by
  obtain ⟨b, _, eB₀, hbdeg, _⟩ := exists_selected_simpleMilnorNorm_presentation_of_prime
    (K := K) (L := B) (hB.symm ▸ hPrime)
  let p := minpolyOfDegree K (Algebra.IsIntegral.isIntegral (R := K) b)
  let E := AdjoinRoot (poly p)
  let eB : B ≃ₐ[K] E := eB₀
  let : IsPurelyInseparable K E := eB.isPurelyInseparable
  have hp₀ : (minpoly K b).natDegree.Prime := hbdeg.symm ▸ (hB.symm ▸ hPrime)
  obtain ⟨a, _, eA₀, hadeg, _⟩ := exists_selected_simpleMilnorNorm_presentation_of_prime
    (K := K) (L := A) (hA.symm ▸ hPrime)
  let h := minpolyOfDegree K (Algebra.IsIntegral.isIntegral (R := K) a)
  let H := AdjoinRoot (poly h)
  let eA : A ≃ₐ[K] H := eA₀
  let j : E →+* D := (algebraMap B D).comp eB.symm.toRingHom
  have hj : j.comp (algebraMap K E) = algebraMap K D := by
    apply RingHom.ext
    intro c
    change algebraMap B D (eB.symm (algebraMap K E c)) = algebraMap K D c
    rw [eB.symm.commutes, ← IsScalarTower.algebraMap_apply K B D]
  let : Algebra E D := j.toAlgebra
  have : IsScalarTower K E D := IsScalarTower.of_algebraMap_eq fun c =>
    (RingHom.congr_fun hj c).symm
  let jA : H →ₐ[K] D := (IsScalarTower.toAlgHom K A D).comp eA.symm.toAlgHom
  let α : D := jA (AdjoinRoot.root (poly h))
  have hα : IsIntegral K α := (AdjoinRoot.isIntegral_root (ne_zero h)).map jA
  have hminK : minpoly K α = poly h := by
    change minpoly K (jA (AdjoinRoot.root (poly h))) = poly h
    rw [minpoly.algHom_eq jA jA.injective, AdjoinRoot.minpoly_root (ne_zero h),
      (monic h).leadingCoeff, inv_one, Polynomial.C_1, mul_one]
  let q₀ := minpolyOfDegree E hα.tower_top
  have hqdiv : poly q₀ ∣ (poly h).map (algebraMap K E) := by
    have hd := minpoly.dvd_map_of_isScalarTower K E α
    rw [hminK] at hd
    exact hd
  let q : {q : Σ f : ℕ, MonicIrreducibleOfDegree E f //
      poly q.2 ∣ (poly h).map (algebraMap K E)} := ⟨⟨_, q₀⟩, hqdiv⟩
  let Q := AdjoinRoot (poly q.1.2)
  have hrootQ : (poly q.1.2).eval₂ j (jA (AdjoinRoot.root (poly h))) = 0 := by
    change aeval α (minpoly E α) = 0
    exact minpoly.aeval E α
  obtain ⟨τ, hτB, hτA⟩ :=
    exists_primePurePair_quotientEquiv p h q eB eA hrootQ hgen
  have hpow := minpoly.map_eq_pow_multiplicity_of_isPurelyInseparable E α hα
  rw [hminK] at hpow
  have hqDegreeDiv : (poly q.1.2).natDegree ∣ finrank K A := by
    change (minpoly E α).natDegree ∣ finrank K A
    refine ⟨multiplicity (minpoly E α) ((poly h).map (algebraMap K E)), ?_⟩
    have hd := congrArg Polynomial.natDegree hpow
    simp only [Polynomial.natDegree_map, Polynomial.natDegree_pow] at hd
    have hAH : (poly h).natDegree = finrank K A := hadeg
    exact hAH.symm.trans (hd.trans (Nat.mul_comm _ _))
  have hBDq : finrank B D = (poly q.1.2).natDegree := by
    calc
      finrank B D = finrank E Q :=
        Algebra.finrank_eq_of_equiv_equiv eB.toRingEquiv τ hτB.symm
      _ = (poly q.1.2).natDegree := by
        rw [(AdjoinRoot.powerBasis (ne_zero q.1.2)).finrank, AdjoinRoot.powerBasis_dim]
  have hdivBD : finrank B D ∣ ell := by
    rw [hBDq]
    exact hA ▸ hqDegreeDiv
  have hADBD : finrank A D = finrank B D := mul_left_cancel₀ hPrime.ne_zero (by
    have hd := (finrank_mul_finrank K A D).trans (finrank_mul_finrank K B D).symm
    simpa only [hA, hB] using hd)
  have hdivAD : finrank A D ∣ ell := hADBD.symm ▸ hdivBD
  let : IsPurelyInseparable A D :=
    primeCoherence_isPurelyInseparable_of_adjoin_range_eq_top (K := K) hgen
  let : IsPurelyInseparable B D :=
    primeCoherence_isPurelyInseparable_of_adjoin_range_eq_top (K := K)
      (primeCoherence_adjoin_range_swap hgen)
  exact primePurePair_of_quotientEquiv p h q ell hPrime hA hB hp₀ hdivBD hdivAD
    eB eA τ hτB hτA x

/-- The actual pure polynomial diamond supplies the exact compositum callback
used by the pure chosen-norm induction. -/
theorem nativePurePrimeNormDiamond (p : ℕ) [Fact p.Prime] :
    NativePurePrimeNormDiamond.{u} p := by
  intro K P Q L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP hQ
  dsimp only
  let C := IntermediateField.adjoin P (Set.range (algebraMap Q L))
  let : Algebra Q C := (adjoinRangeFactor Q P L).toAlgebra
  let : IsScalarTower Q C L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : FiniteDimensional P C :=
    finiteDimensional_adjoin_range_of_finiteDimensional K Q P L
  let : FiniteDimensional Q L := FiniteDimensional.right K Q L
  let : FiniteDimensional Q C := FiniteDimensional.left Q C L
  have : IsScalarTower K C L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower K Q C := IsScalarTower.of_algebraMap_eq fun a => by
    apply (algebraMap C L).injective
    rw [← IsScalarTower.algebraMap_apply K C L,
      ← IsScalarTower.algebraMap_apply Q C L,
      ← IsScalarTower.algebraMap_apply K Q L]
  intro x
  have hgen : adjoin P (Set.range (algebraMap Q C)) = ⊤ :=
    adjoin_range_adjoinRangeFactor_eq_top Q P L
  exact (milnorKNormRing_comp_of_isPurelyInseparable_prime_pair
    (K := K) (A := P) (B := Q) (D := C) p Fact.out hP hQ hgen x).symm

end Stacks.Chow

end
