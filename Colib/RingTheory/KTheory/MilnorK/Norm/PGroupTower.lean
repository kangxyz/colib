/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.FieldTheory.PGroupNormalPrimePresentation
public import Colib.RingTheory.KTheory.MilnorK.Norm.PrimeTower
public import Colib.RingTheory.KTheory.MilnorK.Norm.TowerFactorTransport

/-!
# Native simple-norm towers inside a finite Galois p-group ambient

Strong induction on the actual lower polynomial degree is simultaneous over all
characteristic-zero base fields. A nontrivial lower field contains an actual
normal-prime subfield. The normal-prime tower identities and the smaller relative
tower reduce the result to literal coefficient transport of the relative factor.

The original quotient fields, simple norms and coefficient-factor maps are retained.
The only new ambient algebra action is induced by the actual composite embedding,
with its compatibility proved. The ambient field has an independent universe.
There is no presentation-independence, tower-compatibility or lower-degree norm
hypothesis in the public final statements.
-/

@[expose] public noncomputable section

open Polynomial

universe u v

namespace Stacks.Chow

open MonicIrreducibleOfDegree
attribute [local instance] Ideal.Quotient.field

attribute [local instance] towerTransport_nativeIrreducible

/-- The induction motive quantifies over the base field before choosing the relative base. -/
private theorem simpleMilnorNorm_eq_pGroup_tower_induction (D : ℕ) :
    ∀ (k : Type u) [Field k] [CharZero k] {d e : ℕ}
      (p : MonicIrreducibleOfDegree k d) (h : MonicIrreducibleOfDegree k e),
      (poly p).natDegree = D →
      ∀ (f : AdjoinRoot (poly p) →ₐ[k] AdjoinRoot (poly h))
        (Ω : Type v) [Field Ω] [Algebra k Ω] [FiniteDimensional k Ω] [IsGalois k Ω]
        (ℓ : ℕ) [Fact ℓ.Prime],
        IsPGroup ℓ (Ω ≃ₐ[k] Ω) →
        (AdjoinRoot (poly h) →ₐ[k] Ω) →
        ∀ x : MilnorKRing (AdjoinRoot (poly h)),
          simpleMilnorNorm h x =
            simpleMilnorNorm p
              (simpleMilnorNorm (AdjoinRoot.towerFactor (poly p) (poly h) f).1.2
                (milnorKRingMap
                  (AdjoinRoot.map (algebraMap k (AdjoinRoot (poly p)))
                    (poly h) (poly (AdjoinRoot.towerFactor (poly p) (poly h) f).1.2)
                    (AdjoinRoot.towerFactor (poly p) (poly h) f).2) x)) := by
  induction D using Nat.strong_induction_on with
  | h D ih =>
    intro k _ _ d e p h hd f Ω _ _ _ _ ℓ _ hG j x
    by_cases hp : (poly p).natDegree = 1
    · exact simpleMilnorNorm_eq_tower_of_lower_natDegree_eq_one p h f hp x
    have hpone : 1 < (poly p).natDegree := by
      have hpos := (irreducible p).natDegree_pos
      omega
    let hpFinite : FiniteDimensional k (AdjoinRoot (poly p)) := (monic p).finite_adjoinRoot
    have hdim : 1 < Module.finrank k (AdjoinRoot (poly p)) := by
      rw [(AdjoinRoot.powerBasis (ne_zero p)).finrank]
      exact hpone
    obtain ⟨r, hrmonic, hrirred, hrnormal, hrdegree, ⟨g⟩⟩ :=
      Field.exists_normal_prime_presentation_of_isPGroup_embedding ℓ hG (j.comp f) hdim
    let hrFact : Fact (Irreducible r) := ⟨hrirred⟩
    let a : MonicIrreducibleOfDegree k ℓ := ⟨r, hrmonic, hrirred, hrdegree⟩
    let hrNormal : Normal k (AdjoinRoot (poly a)) := hrnormal
    let g' : AdjoinRoot (poly a) →ₐ[k] AdjoinRoot (poly p) := g
    let A := AdjoinRoot (poly a)
    let qP : {q : Σ n : ℕ, MonicIrreducibleOfDegree A n //
        poly q.2 ∣ (poly p).map (algebraMap k A)} :=
      AdjoinRoot.towerFactor (poly a) (poly p) g'
    let qH : {q : Σ n : ℕ, MonicIrreducibleOfDegree A n //
        poly q.2 ∣ (poly h).map (algebraMap k A)} :=
      AdjoinRoot.towerFactor (poly a) (poly h) (f.comp g')
    let hP : Fact (Irreducible (poly qP.1.2)) := ⟨irreducible qP.1.2⟩
    let hH : Fact (Irreducible (poly qH.1.2)) := ⟨irreducible qH.1.2⟩
    let fA : AdjoinRoot (poly qP.1.2) →ₐ[A] AdjoinRoot (poly qH.1.2) :=
      AdjoinRoot.towerFactorEmbeddingAlgHom (poly a) (poly p) (poly h) g' f
    let qR : {q : Σ n : ℕ, MonicIrreducibleOfDegree (AdjoinRoot (poly qP.1.2)) n //
        poly q.2 ∣ (poly qH.1.2).map (algebraMap A (AdjoinRoot (poly qP.1.2)))} :=
      @AdjoinRoot.towerFactor A (AdjoinRoot.instField (f := poly a))
        (poly qP.1.2) (poly qH.1.2) hP hH fA
    let qD := AdjoinRoot.towerFactor (poly p) (poly h) f
    let eH := AdjoinRoot.towerFactorRingEquiv (poly a) (poly h) (f.comp g')
    let iA : A →ₐ[k] Ω := (j.comp f).comp g'
    let hACharZero : CharZero A :=
      charZero_of_injective_algebraMap (algebraMap k A).injective
    let hAAlgebra : Algebra A Ω := iA.toRingHom.toAlgebra
    let hAScalarTower : IsScalarTower k A Ω :=
      IsScalarTower.of_algebraMap_eq (fun c => (iA.commutes c).symm)
    let hAFinite : FiniteDimensional A Ω := FiniteDimensional.right k A Ω
    let hAGalois : IsGalois A Ω := IsGalois.tower_top_of_isGalois k A Ω
    have hGA : IsPGroup ℓ (Ω ≃ₐ[A] Ω) :=
      hG.of_injective (AlgEquiv.restrictScalarsHom k)
        (AlgEquiv.restrictScalarsHom_injective k)
    let jA : AdjoinRoot (poly qH.1.2) →ₐ[A] Ω :=
      { j.toRingHom.comp eH.toRingHom with
        commutes' := fun c => by
          change j (eH (algebraMap A (AdjoinRoot (poly qH.1.2)) c)) = iA c
          rw [AdjoinRoot.towerFactorRingEquiv_algebraMap]
          rfl }
    have hsmall : (poly qP.1.2).natDegree < D := by
      rw [← hd]
      exact AdjoinRoot.towerFactor_natDegree_lt (poly a) (poly p) g'
        (by rw [natDegree_eq]; exact (Fact.out : ℓ.Prime).one_lt)
    let mH := AdjoinRoot.map (algebraMap k A) (poly h) (poly qH.1.2) qH.2
    let mR := AdjoinRoot.map (algebraMap A (AdjoinRoot (poly qP.1.2)))
      (poly qH.1.2) (poly qR.1.2) qR.2
    let mD := AdjoinRoot.map (algebraMap k (AdjoinRoot (poly p)))
      (poly h) (poly qD.1.2) qD.2
    have hrelative := ih (poly qP.1.2).natDegree hsmall A qP.1.2 qH.1.2 rfl fA
      Ω ℓ hGA jA (milnorKRingMap mH x)
    have htransport := simpleMilnorNorm_towerFactorAssoc_map
      (k := k) (d := d) (e := e) p h f (c := ℓ) a g'
    have hnorm := htransport (milnorKRingMap mR (milnorKRingMap mH x))
    have hmaps := milnorKRingMap_towerFactorAssoc_map_map
      (k := k) (d := d) (e := e) p h f (c := ℓ) a g' x
    dsimp only at hnorm hmaps
    have hnormOuter := congrArg (simpleMilnorNorm p) hnorm
    have hfirst := simpleMilnorNorm_eq_prime_tower a (Fact.out : ℓ.Prime)
      h (f.comp g') x
    have hrelativeOuter := congrArg (simpleMilnorNorm a) hrelative
    have hprime := simpleMilnorNorm_prime_tower a (Fact.out : ℓ.Prime) p g'
      (simpleMilnorNorm qR.1.2 (milnorKRingMap mR (milnorKRingMap mH x)))
    have hmapsOuter :=
      congrArg (fun y => simpleMilnorNorm p (simpleMilnorNorm qD.1.2 y)) hmaps
    have hfirstRelative := hfirst.trans hrelativeOuter
    have hthroughPrime := hfirstRelative.trans hprime
    have hthroughTransport := hthroughPrime.trans hnormOuter
    have hfinal := hthroughTransport.trans hmapsOuter
    exact hfinal

variable {k : Type u} [Field k] [CharZero k] {d e : ℕ}
  (p : MonicIrreducibleOfDegree k d) (h : MonicIrreducibleOfDegree k e)
  (f : AdjoinRoot (poly p) →ₐ[k] AdjoinRoot (poly h))
  {Ω : Type v} [Field Ω] [Algebra k Ω] [FiniteDimensional k Ω] [IsGalois k Ω]
  (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[k] Ω))
  (j : AdjoinRoot (poly h) →ₐ[k] Ω)

include hG j

local notation "E" => AdjoinRoot (poly p)
local notation "H" => AdjoinRoot (poly h)
local notation "q" => AdjoinRoot.towerFactor (poly p) (poly h) f
local notation "Q" => AdjoinRoot (poly q.1.2)

/-- The native simple norm factors through the given lower field in a p-group ambient.
No primality or normality of the lower field and no lower-degree norm premise is required. -/
theorem simpleMilnorNorm_eq_pGroup_tower (x : MilnorKRing H) :
    simpleMilnorNorm h x =
      simpleMilnorNorm p
        (simpleMilnorNorm q.1.2
          (milnorKRingMap
            (AdjoinRoot.map (algebraMap k E) (poly h) (poly q.1.2) q.2) x)) :=
  simpleMilnorNorm_eq_pGroup_tower_induction (poly p).natDegree
    k p h rfl f Ω ℓ hG j x

/-- The same identity on the actual upper quotient, using its original top-field map. -/
theorem simpleMilnorNorm_pGroup_tower (z : MilnorKRing Q) :
    simpleMilnorNorm p (simpleMilnorNorm q.1.2 z) =
      simpleMilnorNorm h
        (milnorKRingMap (AdjoinRoot.towerFactorRingEquiv (poly p) (poly h) f).toRingHom z) := by
  rw [simpleMilnorNorm_eq_pGroup_tower p h f ℓ hG j]
  apply congrArg (fun y => simpleMilnorNorm p (simpleMilnorNorm q.1.2 y))
  rw [← AdjoinRoot.towerFactorRingEquiv_symm_toRingHom, milnorKRingMap_comp_apply]
  have hcomp :
      (AdjoinRoot.towerFactorRingEquiv (poly p) (poly h) f).symm.toRingHom.comp
          (AdjoinRoot.towerFactorRingEquiv (poly p) (poly h) f).toRingHom =
        RingHom.id Q := by
    apply RingHom.ext
    intro b
    exact (AdjoinRoot.towerFactorRingEquiv (poly p) (poly h) f).symm_apply_apply b
  exact ((congrArg (fun φ : Q →+* Q => milnorKRingMap φ z) hcomp).trans
    (milnorKRingMap_id_apply z)).symm

/-- Equality of the whole-ring native additive maps on the original top field. -/
theorem simpleMilnorNorm_eq_comp_pGroup_tower :
    simpleMilnorNorm h =
      (simpleMilnorNorm p).comp
        ((simpleMilnorNorm q.1.2).comp
          (milnorKRingMap
            (AdjoinRoot.map (algebraMap k E) (poly h) (poly q.1.2) q.2)).toAddMonoidHom) := by
  ext x
  exact simpleMilnorNorm_eq_pGroup_tower p h f ℓ hG j x

/-- Equality of the whole-ring native additive maps on the actual upper quotient. -/
theorem simpleMilnorNorm_comp_simpleMilnorNorm_pGroup_tower :
    (simpleMilnorNorm p).comp (simpleMilnorNorm q.1.2) =
      (simpleMilnorNorm h).comp
        (milnorKRingMap
          (AdjoinRoot.towerFactorRingEquiv (poly p) (poly h) f).toRingHom).toAddMonoidHom := by
  ext z
  exact simpleMilnorNorm_pGroup_tower p h f ℓ hG j z

end Stacks.Chow

end
