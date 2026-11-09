/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.RationalDegreeOne
public import Colib.RingTheory.KTheory.MilnorK.Norm.RationalLinearResidue
public import Colib.RingTheory.KTheory.MilnorK.Norm.RationalScalarBaseChange
public import Colib.RingTheory.KTheory.MilnorK.Residue.TensorBranchLinear

/-!
# The full native finite-place square for a normal-prime rational norm

The original finite residue is linearized over its own actual residue field.
The complete rational scalar-factor formula is reindexed by the actual tensor
swap on the native factor subtypes. Separability proves that every original
coefficient-factor multiplicity is one before any weight is removed.

Each opposite factor is normal and has degree one or the original prime degree.
The corresponding native linear norm-residue square and chosen/simple-norm
comparison are proved in those two cases. The actual tensor quotient square
then identifies each summand with the original upper residue.

The proof route is the finite-place argument recorded in
`Aglib/KTheory/MilnorK/Norm/Polynomial/RationalFinitePrime.lean` at revision
`52e09db47998f139064acf48a2d3a64494d0dd9a`. Its norm and residue models are not
imported or copied. All operations here are the existing native operations.
No norm tower law, general presentation independence, selected-branch coverage,
residue compatibility, or chosen-norm comparison is assumed.
-/

@[expose] public noncomputable section

open Polynomial
open scoped RatFunc
attribute [local instance] Polynomial.algebra

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

local instance rationalFiniteResidue_linearMaximal {F : Type u} [Field F] (a : F) :
    (Ideal.span ({X - C a} : Set F[X])).IsMaximal :=
  isMaximal_span_singleton_of_irreducible_polynomial (irreducible_X_sub_C a)

local instance rationalFiniteResidue_nativeIrreducible {F : Type u} [Field F]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d) : Fact (Irreducible (poly p)) :=
  ⟨irreducible p⟩

local instance rationalFiniteResidue_rootFinite {F : Type u} [Field F]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d) : Module.Finite F (AdjoinRoot (poly p)) :=
  (AdjoinRoot.powerBasis (ne_zero p)).finite

local instance rationalFiniteResidue_rationalFinite {F : Type u} [Field F]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d) :
    Module.Finite (RatFunc F) (RatFunc (AdjoinRoot (poly p))) :=
  FiniteDimensional.of_finrank_pos (by
    rw [AdjoinRoot.finrank_ratFunc_adjoinRoot]
    exact (irreducible p).natDegree_pos)

variable {k K : Type u} [Field k] [Field K] {d e : ℕ}

/-- Every native factor of a separable coefficient image has its actual
polynomial multiplicity equal to one. The divisibility and finite multiplicity
arguments are both retained. -/
theorem multiplicity_eq_one_of_nativeFactor_dvd_map_of_separable
    (φ : k →+* K) (p : MonicIrreducibleOfDegree k d) (hs : (poly p).Separable)
    (q : MonicIrreducibleOfDegree K e) (hq : poly q ∣ (poly p).map φ) :
    multiplicity (poly q) ((poly p).map φ) = 1 := by
  apply Nat.le_antisymm
  · apply multiplicity_le_of_emultiplicity_le
    exact emultiplicity_le_one_of_separable (irreducible q).not_isUnit hs.map
  · exact Nat.succ_le_of_lt (multiplicity_pos_of_dvd hq
      (FiniteMultiplicity.of_not_isUnit (irreducible q).not_isUnit
        (Polynomial.map_ne_zero (ne_zero p))))

/-- Every actual scalar factor of the original normal-prime root field has
the native linear square with its simple polynomial norm. The split degree-one
case and the normal prime-degree case are both proved, not supplied as inputs. -/
theorem monicIrreducibleResidue_X_sub_C_milnorKNorm_ratFunc_of_scalarFactor
    [CharZero k] (φ : k →+* K) (p : MonicIrreducibleOfDegree k d) (hp : d.Prime)
    [Normal k (AdjoinRoot (poly p))]
    (q : MonicIrreducibleOfDegree K e) (hq : poly q ∣ (poly p).map φ)
    (a : K) (n : ℕ) (x : MilnorKTheory (RatFunc (AdjoinRoot (poly q))) (n + 1)) :
    milnorKRingMap (quotientSpanXSubCAlgEquiv a).toRingHom
        (monicIrreducibleResidue
          (⟨X - C a, monic_X_sub_C a, irreducible_X_sub_C a, natDegree_X_sub_C a⟩ :
            MonicIrreducibleOfDegree K 1)
          (milnorKNorm (RatFunc K) (RatFunc (AdjoinRoot (poly q)))
            (n + 1) x : MilnorKRing (RatFunc K))) =
      simpleMilnorNorm q
        (milnorKRingMap
          (quotientSpanXSubCAlgEquiv (algebraMap K (AdjoinRoot (poly q)) a)).toRingHom
          (monicIrreducibleResidue
            (⟨X - C (algebraMap K (AdjoinRoot (poly q)) a),
              monic_X_sub_C _, irreducible_X_sub_C _, natDegree_X_sub_C _⟩ :
                MonicIrreducibleOfDegree (AdjoinRoot (poly q)) 1)
            (x : MilnorKRing (RatFunc (AdjoinRoot (poly q)))))) := by
  let rationalFiniteResidue_scalarAlgebra : Algebra k K := φ.toAlgebra
  let rationalFiniteResidue_scalarCharZero : CharZero K :=
    charZero_of_injective_algebraMap (algebraMap k K).injective
  let ep : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] AdjoinRoot (poly p) :=
    { toRingEquiv := RingEquiv.refl _
      commutes' := fun _ => rfl }
  let rationalFiniteResidue_sourceQuotientNormal :
      Normal k (k[X] ⧸ Ideal.span {poly p}) := Normal.of_algEquiv ep.symm
  let eq : (K[X] ⧸ Ideal.span {poly q}) ≃ₐ[K] AdjoinRoot (poly q) :=
    { toRingEquiv := RingEquiv.refl _
      commutes' := fun _ => rfl }
  let rationalFiniteResidue_targetQuotientNormal :
      Normal K (K[X] ⧸ Ideal.span {poly q}) :=
    normal_quotient_of_dvd_map_of_normal φ p q hq
  let rationalFiniteResidue_scalarNormal : Normal K (AdjoinRoot (poly q)) :=
    Normal.of_algEquiv eq
  have hdegree : e = 1 ∨ e = d :=
    degree_eq_one_or_eq_of_dvd_map_of_normal_prime φ p hp q hq
  have hlinear :
      milnorKRingMap (quotientSpanXSubCAlgEquiv a).toRingHom
          (monicIrreducibleResidue
            (⟨X - C a, monic_X_sub_C a, irreducible_X_sub_C a, natDegree_X_sub_C a⟩ :
              MonicIrreducibleOfDegree K 1)
            (milnorKNorm (RatFunc K) (RatFunc (AdjoinRoot (poly q)))
              (n + 1) x : MilnorKRing (RatFunc K))) =
        milnorKNormRing K (AdjoinRoot (poly q))
          (milnorKRingMap
            (quotientSpanXSubCAlgEquiv (algebraMap K (AdjoinRoot (poly q)) a)).toRingHom
            (monicIrreducibleResidue
              (⟨X - C (algebraMap K (AdjoinRoot (poly q)) a),
                monic_X_sub_C _, irreducible_X_sub_C _, natDegree_X_sub_C _⟩ :
                  MonicIrreducibleOfDegree (AdjoinRoot (poly q)) 1)
              (x : MilnorKRing (RatFunc (AdjoinRoot (poly q)))))) := by
    rcases hdegree with hone | hprime
    · subst e
      exact monicIrreducibleResidue_X_sub_C_milnorKNorm_ratFunc_of_degree_one q a n x
    · exact monicIrreducibleResidue_X_sub_C_milnorKNorm_ratFunc
        q a (hprime.symm ▸ hp) n x
  have hnormDegree : e = 1 ∨ e.Prime := by
    rcases hdegree with hone | hprime
    · exact Or.inl hone
    · exact Or.inr (hprime.symm ▸ hp)
  let y : MilnorKRing (AdjoinRoot (poly q)) :=
    milnorKRingMap
      (quotientSpanXSubCAlgEquiv (algebraMap K (AdjoinRoot (poly q)) a)).toRingHom
      (monicIrreducibleResidue
        (⟨X - C (algebraMap K (AdjoinRoot (poly q)) a),
          monic_X_sub_C _, irreducible_X_sub_C _, natDegree_X_sub_C _⟩ :
            MonicIrreducibleOfDegree (AdjoinRoot (poly q)) 1)
        (x : MilnorKRing (RatFunc (AdjoinRoot (poly q)))))
  have hcomparison :=
    milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_one_or_normal_prime
      q hnormDegree eq.symm y
  change milnorKNormRing K (AdjoinRoot (poly q)) y =
    simpleMilnorNorm q (milnorKRingMap (RingHom.id (AdjoinRoot (poly q))) y) at hcomparison
  exact hlinear.trans (by simpa only [milnorKRingMap_id_apply] using hcomparison)

variable [CharZero k] (p : MonicIrreducibleOfDegree k d) (hp : d.Prime)
  [Normal k (AdjoinRoot (poly p))] (h : MonicIrreducibleOfDegree k e)

include hp

local notation "E" => AdjoinRoot (poly p)
local notation "H" => AdjoinRoot (poly h)

/-- The native finite residue of the original chosen rational norm is the
complete sum over the literal upper factors. Each summand uses the actual
opposite polynomial norm and actual tensor-swap quotient equivalence.
The finite set is exact, and no branch, including a degree-one branch, is omitted. -/
theorem monicIrreducibleResidue_milnorKNorm_ratFunc_eq_sum_tensorSwap
    (S : Finset (Σ f : ℕ, MonicIrreducibleOfDegree E f))
    (hS : ∀ q, q ∈ S ↔ poly q.2 ∣ (poly h).map (algebraMap k E))
    (n : ℕ) (x : MilnorKTheory (RatFunc E) (n + 1)) :
    monicIrreducibleResidue h
        (milnorKNorm (RatFunc k) (RatFunc E) (n + 1) x : MilnorKRing (RatFunc k)) =
      ∑ i ∈ S.attach,
        let q : {q : Σ f : ℕ, MonicIrreducibleOfDegree E f //
            poly q.2 ∣ (poly h).map (algebraMap k E)} := ⟨i.1, (hS i.1).mp i.2⟩
        let r := AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h) q
        simpleMilnorNorm r.1.2
          (milnorKRingMap
            ((AdjoinRoot.tensorSwapFactorQuotientEquiv (poly p) (poly h) q).toRingHom :
              (E[X] ⧸ Ideal.span {poly q.1.2}) →+*
                (H[X] ⧸ Ideal.span {poly r.1.2}))
            (monicIrreducibleResidue i.1.2 (x : MilnorKRing (RatFunc E)))) := by
  classical
  let φ : k →+* H := algebraMap k H
  let b : H := AdjoinRoot.root (poly h)
  let l : MonicIrreducibleOfDegree H 1 :=
    ⟨X - C b, monic_X_sub_C b, irreducible_X_sub_C b, natDegree_X_sub_C b⟩
  let ev : MilnorKRing (RatFunc H) →+ MilnorKRing (k[X] ⧸ Ideal.span {poly h}) :=
    (milnorKRingMap
      ((quotientSpanXSubCAlgEquiv b).toRingHom :
        (H[X] ⧸ Ideal.span {poly l}) →+*
          (k[X] ⧸ Ideal.span {poly h}))).toAddMonoidHom.comp
            (monicIrreducibleResidue l)
  obtain ⟨T, hT⟩ := exists_finset_mem_iff_dvd_map φ (poly p) (ne_zero p)
  let B : S ≃ T :=
    (Equiv.subtypeEquivRight hS).trans
      ((AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h)).trans
        (Equiv.subtypeEquivRight hT).symm)
  let j (t : T) : E →+* AdjoinRoot (poly t.1.2) :=
    AdjoinRoot.map φ (poly p) (poly t.1.2) ((hT t.1).mp t.2)
  let jR (t : T) : RatFunc E →+* RatFunc (AdjoinRoot (poly t.1.2)) :=
    RatFunc.mapRingHom (Polynomial.mapRingHom (j t))
      (Polynomial.nonZeroDivisors_le_comap_mapRingHom (j t))
  have hmult (t : T) : multiplicity (poly t.1.2) ((poly p).map φ) = 1 :=
    multiplicity_eq_one_of_nativeFactor_dvd_map_of_separable φ p
      (irreducible p).separable t.1.2 ((hT t.1).mp t.2)
  have hsum := milnorKNormRing_ratFunc_map_eq_sum_coefficientFactors_of_normal_prime
    φ p hp T hT (x : MilnorKRing (RatFunc E))
  calc
    _ = ev (milnorKRingMap
        (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ))
        (milnorKNormRing (RatFunc k) (RatFunc E) (x : MilnorKRing (RatFunc E)))) :=
      monicIrreducibleResidue_eq_linearResidue_mapRingHom h _
    _ = ev (∑ t ∈ T.attach, (multiplicity (poly t.1.2) ((poly p).map φ) : ℤ) •
        milnorKNormRing (RatFunc H) (RatFunc (AdjoinRoot (poly t.1.2)))
          (milnorKRingMap (jR t) (x : MilnorKRing (RatFunc E)))) :=
      congrArg ev hsum
    _ = ∑ t ∈ T.attach, (multiplicity (poly t.1.2) ((poly p).map φ) : ℤ) •
        ev (milnorKNormRing (RatFunc H) (RatFunc (AdjoinRoot (poly t.1.2)))
          (milnorKRingMap (jR t) (x : MilnorKRing (RatFunc E)))) := by
      simp only [map_sum, map_zsmul]
    _ = ∑ t ∈ T.attach,
        ev (milnorKNormRing (RatFunc H) (RatFunc (AdjoinRoot (poly t.1.2)))
          (milnorKRingMap (jR t) (x : MilnorKRing (RatFunc E)))) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [hmult t, Nat.cast_one, one_zsmul]
    _ = (∑ i ∈ S.attach,
        let q : {q : Σ f : ℕ, MonicIrreducibleOfDegree E f //
            poly q.2 ∣ (poly h).map (algebraMap k E)} := ⟨i.1, (hS i.1).mp i.2⟩
        let r := AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h) q
        simpleMilnorNorm r.1.2
          (milnorKRingMap
            ((AdjoinRoot.tensorSwapFactorQuotientEquiv (poly p) (poly h) q).toRingHom :
              (E[X] ⧸ Ideal.span {poly q.1.2}) →+*
                (H[X] ⧸ Ideal.span {poly r.1.2}))
            (monicIrreducibleResidue i.1.2 (x : MilnorKRing (RatFunc E)))) :
              MilnorKRing (k[X] ⧸ Ideal.span {poly h})) := by
      symm
      simp only [Finset.attach_eq_univ]
      refine Fintype.sum_equiv B _ _ ?_
      intro i
      let q : {q : Σ f : ℕ, MonicIrreducibleOfDegree E f //
          poly q.2 ∣ (poly h).map (algebraMap k E)} := ⟨i.1, (hS i.1).mp i.2⟩
      let r := AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h) q
      let ψ : E →+* AdjoinRoot (poly r.1.2) :=
        AdjoinRoot.map φ (poly p) (poly r.1.2) r.2
      let ψR : RatFunc E →+* RatFunc (AdjoinRoot (poly r.1.2)) :=
        RatFunc.mapRingHom (Polynomial.mapRingHom ψ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom ψ)
      let y : MilnorKTheory (RatFunc (AdjoinRoot (poly r.1.2))) (n + 1) :=
        ⟨milnorKRingMap ψR (x : MilnorKRing (RatFunc E)),
          milnorKRingMap_mem_milnorKGrading ψR x.property⟩
      change simpleMilnorNorm r.1.2
          (milnorKRingMap
            ((AdjoinRoot.tensorSwapFactorQuotientEquiv (poly p) (poly h) q).toRingHom :
              (E[X] ⧸ Ideal.span {poly q.1.2}) →+*
                (H[X] ⧸ Ideal.span {poly r.1.2}))
            (monicIrreducibleResidue q.1.2 (x : MilnorKRing (RatFunc E)))) =
        ev (milnorKNormRing (RatFunc H) (RatFunc (AdjoinRoot (poly r.1.2)))
          (milnorKRingMap ψR (x : MilnorKRing (RatFunc E))))
      have hlinear := monicIrreducibleResidue_X_sub_C_milnorKNorm_ratFunc_of_scalarFactor
        φ p hp r.1.2 r.2 b n y
      have hres := monicIrreducibleResidue_tensorSwapFactor_linear
        (poly p) (poly h) q (x : MilnorKRing (RatFunc E))
      exact (hlinear.trans (congrArg (simpleMilnorNorm r.1.2) hres)).symm

/-- The full native finite-place formula admits an exact finite upper factor
set without assuming any enumeration or coverage data. The same set works in
every homogeneous degree and for every original rational class. -/
theorem exists_finset_monicIrreducibleResidue_milnorKNorm_ratFunc_eq_sum_tensorSwap :
    ∃ (S : Finset (Σ f : ℕ, MonicIrreducibleOfDegree E f))
      (hS : ∀ q, q ∈ S ↔ poly q.2 ∣ (poly h).map (algebraMap k E)),
      ∀ (n : ℕ) (x : MilnorKTheory (RatFunc E) (n + 1)),
        monicIrreducibleResidue h
            (milnorKNorm (RatFunc k) (RatFunc E) (n + 1) x :
              MilnorKRing (RatFunc k)) =
          ∑ i ∈ S.attach,
            let q : {q : Σ f : ℕ, MonicIrreducibleOfDegree E f //
                poly q.2 ∣ (poly h).map (algebraMap k E)} := ⟨i.1, (hS i.1).mp i.2⟩
            let r := AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h) q
            simpleMilnorNorm r.1.2
              (milnorKRingMap
                ((AdjoinRoot.tensorSwapFactorQuotientEquiv
                  (poly p) (poly h) q).toRingHom :
                    (E[X] ⧸ Ideal.span {poly q.1.2}) →+*
                      (H[X] ⧸ Ideal.span {poly r.1.2}))
                (monicIrreducibleResidue i.1.2 (x : MilnorKRing (RatFunc E)))) := by
  obtain ⟨S, hS⟩ :=
    exists_finset_mem_iff_dvd_map (algebraMap k E) (poly h) (ne_zero h)
  exact ⟨S, hS,
    monicIrreducibleResidue_milnorKNorm_ratFunc_eq_sum_tensorSwap p hp h S hS⟩

end Stacks.Chow
