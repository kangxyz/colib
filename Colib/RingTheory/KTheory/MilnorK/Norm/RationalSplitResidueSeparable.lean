/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.FieldTheory.RatFunc.CoefficientGalois
public import Colib.RingTheory.AdjoinRoot.SeparableConstantFactors
public import Colib.RingTheory.AdjoinRoot.TowerFactorGalois
public import Colib.RingTheory.KTheory.MilnorK.Norm.NormalPrimeTrace
public import Colib.RingTheory.KTheory.MilnorK.Norm.PolynomialResidueMap
public import Colib.RingTheory.KTheory.MilnorK.Norm.RationalConstantSeparable

/-!
# The full split finite-place square for a separable normal-prime constant norm

A literal embedding of the constant field into the original residue field is the
split-case input. Restriction of the native rational norm is its actual Galois
trace. At the chosen branch, restriction of residue has multiplicity one by
squarefreeness of the whole constant-cover algebra. The actual quotient map is
an isomorphism, so it can be inverted without any torsion cancellation.

The original Galois group permutes the literal upper factors bijectively. The
full finite sum is therefore reindexed by all actual tensor-swap factors. Every
summand uses the existing simple norm and actual quotient equivalence. No finite
instance on an individual localization, closed-point separability, extra norm
square, norm tower law or Milnor torsion-freeness is used.
-/

@[expose] public noncomputable section

open Polynomial Module
open scoped RatFunc
attribute [local instance] Polynomial.algebra

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

/-- The native precomposition, elaborated with the explicit polynomial instances
used by the lower branch lemmas. This is definitionally the original composition. -/
abbrev rationalSplitComp {K : Type u} [Field K] (a b : K[X])
    [Fact (Irreducible a)] [Fact (Irreducible b)]
    (g : AdjoinRoot a →ₐ[K] AdjoinRoot b) (σ : Gal(AdjoinRoot a/K)) :
    AdjoinRoot a →ₐ[K] AdjoinRoot b :=
  g.comp σ.toAlgHom

attribute [local instance] Ideal.Quotient.field

local instance rationalSplit_nativeIrreducible {F : Type u} [Field F]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d) : Fact (Irreducible (poly p)) :=
  ⟨irreducible p⟩

local instance rationalSplit_finiteRoot {F : Type u} [Field F]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d) : Module.Finite F (AdjoinRoot (poly p)) :=
  (AdjoinRoot.powerBasis (ne_zero p)).finite

local instance rationalSplit_finiteRatFuncRoot {F : Type u} [Field F]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d) :
    Module.Finite (RatFunc F) (RatFunc (AdjoinRoot (poly p))) :=
  FiniteDimensional.of_finrank_pos (by
    rw [AdjoinRoot.finrank_ratFunc_adjoinRoot]
    exact (irreducible p).natDegree_pos)

variable {k : Type u} [Field k] {d e : ℕ}
  (p : MonicIrreducibleOfDegree k d) (hsep : (poly p).Separable) (hp : d.Prime)
  [Normal k (AdjoinRoot (poly p))]

local notation "E" => AdjoinRoot (poly p)

include hsep hp

/-- The native rational norm restricts to the trace indexed by the original
constant Galois group. The underlying maps are literal rational coefficient maps. -/
theorem milnorKNormRing_ratFunc_map_eq_sum_coefficientGal_of_separable
    (x : MilnorKRing (RatFunc E)) :
    milnorKRingMap (algebraMap (RatFunc k) (RatFunc E))
        (milnorKNormRing (RatFunc k) (RatFunc E) x) =
      ∑ σ : Gal(E/k), milnorKRingMap
        (RatFunc.mapRingHom (Polynomial.mapRingHom σ.toRingHom)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom σ.toRingHom)) x := by
  classical
  let : Algebra.IsSeparable k E :=
    AdjoinRoot.isSeparable_of_polynomial_separable _ hsep
  let : IsGalois k E := ⟨⟩
  let : Normal (RatFunc k) (RatFunc E) :=
    AdjoinRoot.normal_ratFunc_adjoinRoot (poly p) (monic p)
  let : Algebra.IsSeparable (RatFunc k) (RatFunc E) :=
    isSeparable_ratFunc_adjoinRoot_of_separable p hsep
  let : IsGalois (RatFunc k) (RatFunc E) := ⟨⟩
  have hpR : Nat.Prime (finrank (RatFunc k) (RatFunc E)) := by
    rw [AdjoinRoot.finrank_ratFunc_adjoinRoot, natDegree_eq]
    exact hp
  rw [milnorKNormRing_map_eq_sum_gal_of_normal_prime hpR]
  symm
  exact Fintype.sum_bijective RatFunc.coefficientGal RatFunc.coefficientGal_bijective
    _ _ (fun σ => by rw [RatFunc.coefficientGal_toRingHom])

variable (h : MonicIrreducibleOfDegree k e)
  (f : AdjoinRoot (poly p) →ₐ[k] AdjoinRoot (poly h))

local notation "H" => AdjoinRoot (poly h)
local notation "q₀" => AdjoinRoot.towerFactor (poly p) (poly h) f
local notation "θ₀" => AdjoinRoot.towerFactorRingEquiv (poly p) (poly h) f

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The split residue formula before reindexing. Every summand is an original
upper residue transported by its actual degree-one branch isomorphism. -/
theorem monicIrreducibleResidue_milnorKNormRing_ratFunc_eq_sum_gal_of_split
    (x : MilnorKRing (RatFunc E)) :
    monicIrreducibleResidue h (milnorKNormRing (RatFunc k) (RatFunc E) x) =
      ∑ σ : Gal(E/k),
        let g : E →ₐ[k] H := rationalSplitComp (poly p) (poly h) f σ
        let q : {q : Σ a : ℕ, MonicIrreducibleOfDegree E a //
            poly q.2 ∣ (poly h).map (algebraMap k E)} :=
          AdjoinRoot.towerFactor (poly p) (poly h) g
        let τ : (E[X] ⧸ Ideal.span {poly q.1.2}) →+*
            (k[X] ⧸ Ideal.span {poly h}) :=
          (AdjoinRoot.towerFactorRingEquiv (poly p) (poly h) g).toRingHom
        milnorKRingMap τ (monicIrreducibleResidue q.1.2 x) := by
  classical
  let z := milnorKNormRing (RatFunc k) (RatFunc E) x
  have hm : multiplicity (poly q₀.1.2)
      ((poly h).map (algebraMap k E)) = 1 :=
    AdjoinRoot.multiplicity_eq_one_of_dvd_map_separable_constant
      (poly p) (poly h) hsep _ (irreducible q₀.1.2) q₀.2
  have hres := monicIrreducibleResidue_mapRingHom (algebraMap k E) h q₀.1.2 q₀.2 z
  rw [hm, Nat.cast_one, one_zsmul, ← RatFunc.algebraMap_eq_mapRingHom] at hres
  have hinverse : (θ₀).toRingHom.comp
      (AdjoinRoot.map (algebraMap k E) (poly h) (poly q₀.1.2) q₀.2) =
        RingHom.id H := by
    apply RingHom.ext
    intro a
    exact AdjoinRoot.towerFactorRingEquiv_map (poly p) (poly h) f a
  have hres' :
      milnorKRingMap (θ₀).toRingHom
          (monicIrreducibleResidue q₀.1.2
            (milnorKRingMap (algebraMap (RatFunc k) (RatFunc E)) z)) =
        monicIrreducibleResidue h z := by
    let ι : (k[X] ⧸ Ideal.span {poly h}) →+*
        (E[X] ⧸ Ideal.span {poly q₀.1.2}) :=
      AdjoinRoot.map (algebraMap k E) (poly h) (poly q₀.1.2) q₀.2
    let τ : (E[X] ⧸ Ideal.span {poly q₀.1.2}) →+*
        (k[X] ⧸ Ideal.span {poly h}) := (θ₀).toRingHom
    have hleft := congrArg (fun y : MilnorKRing (E[X] ⧸ Ideal.span {poly q₀.1.2}) =>
      milnorKRingMap τ y) hres
    have hc := milnorKRingMap_comp_apply ι τ (monicIrreducibleResidue h z)
    have hi : τ.comp ι = RingHom.id (k[X] ⧸ Ideal.span {poly h}) := hinverse
    have he := congrArg
      (fun ψ : (k[X] ⧸ Ideal.span {poly h}) →+* (k[X] ⧸ Ideal.span {poly h}) =>
        milnorKRingMap ψ (monicIrreducibleResidue h z)) hi
    exact hleft.trans (hc.trans (he.trans
      (milnorKRingMap_id_apply (monicIrreducibleResidue h z))))
  rw [← hres']
  change milnorKRingMap (θ₀).toRingHom
      (monicIrreducibleResidue q₀.1.2
        (milnorKRingMap (algebraMap (RatFunc k) (RatFunc E))
          (milnorKNormRing (RatFunc k) (RatFunc E) x))) = _
  rw [milnorKNormRing_ratFunc_map_eq_sum_coefficientGal_of_separable p hsep hp]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  let q := AdjoinRoot.towerFactor (poly p) (poly h)
    (rationalSplitComp (poly p) (poly h) f σ)
  have hmap : (poly q.1.2).map σ.toRingHom = poly q₀.1.2 :=
    AdjoinRoot.towerFactor_compGal_poly_map (poly p) (poly h) f σ
  have hdiv : poly q₀.1.2 ∣ (poly q.1.2).map σ.toRingHom := by rw [hmap]
  have hmσ : multiplicity (poly q₀.1.2) ((poly q.1.2).map σ.toRingHom) = 1 := by
    rw [hmap]
    exact (irreducible q₀.1.2).multiplicity_self
  rw [monicIrreducibleResidue_mapRingHom σ.toRingHom q.1.2 q₀.1.2 hdiv x,
    hmσ, Nat.cast_one, one_zsmul]
  have hcomp : (θ₀).toRingHom.comp
      (AdjoinRoot.map σ.toRingHom (poly q.1.2) (poly q₀.1.2) hdiv) =
        (AdjoinRoot.towerFactorRingEquiv (poly p) (poly h)
          (rationalSplitComp (poly p) (poly h) f σ)).toRingHom := by
    rw [← AdjoinRoot.towerFactorCompGalRingEquiv_toRingHom]
    apply RingHom.ext
    intro a
    exact (θ₀).apply_symm_apply _
  let μ : (E[X] ⧸ Ideal.span {poly q.1.2}) →+*
      (E[X] ⧸ Ideal.span {poly q₀.1.2}) :=
    AdjoinRoot.map σ.toRingHom (poly q.1.2) (poly q₀.1.2) hdiv
  let τ : (E[X] ⧸ Ideal.span {poly q₀.1.2}) →+*
      (k[X] ⧸ Ideal.span {poly h}) := (θ₀).toRingHom
  let υ : (E[X] ⧸ Ideal.span {poly q.1.2}) →+*
      (k[X] ⧸ Ideal.span {poly h}) :=
    (AdjoinRoot.towerFactorRingEquiv (poly p) (poly h)
      (rationalSplitComp (poly p) (poly h) f σ)).toRingHom
  have hc := milnorKRingMap_comp_apply μ τ (monicIrreducibleResidue q.1.2 x)
  have hi : τ.comp μ = υ := hcomp
  have he := congrArg
    (fun ψ : (E[X] ⧸ Ideal.span {poly q.1.2}) →+* (k[X] ⧸ Ideal.span {poly h}) =>
      milnorKRingMap ψ (monicIrreducibleResidue q.1.2 x)) hi
  exact hc.trans he

omit hsep hp in
private theorem rationalSplit_simpleNorm_degree_one {F : Type u} [Field F] {a : ℕ}
    (r : MonicIrreducibleOfDegree F a) (hr : (poly r).natDegree = 1)
    (ε : AdjoinRoot (poly r) ≃ₐ[F] F) (z : MilnorKRing (AdjoinRoot (poly r))) :
    simpleMilnorNorm r z = milnorKRingMap ε.toRingHom z := by
  have ha : a = 1 := (natDegree_eq r).symm.trans hr
  subst a
  exact simpleMilnorNorm_eq_map_of_degree_one r ε z

include f in
/-- The split square with the exact complete native factor set and the original
opposite simple norms. No separability of the finite place is required. -/
theorem monicIrreducibleResidue_milnorKNormRing_ratFunc_eq_sum_tensorSwap_of_split
    (S : Finset (Σ a : ℕ, MonicIrreducibleOfDegree E a))
    (hS : ∀ q, q ∈ S ↔ poly q.2 ∣ (poly h).map (algebraMap k E))
    (x : MilnorKRing (RatFunc E)) :
    monicIrreducibleResidue h (milnorKNormRing (RatFunc k) (RatFunc E) x) =
      ∑ i ∈ S.attach,
        let q : {q : Σ a : ℕ, MonicIrreducibleOfDegree E a //
            poly q.2 ∣ (poly h).map (algebraMap k E)} := ⟨i.1, (hS i.1).mp i.2⟩
        let r := AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h) q
        simpleMilnorNorm r.1.2
          (@milnorKRingMap
            (E[X] ⧸ Ideal.span {poly q.1.2}) (H[X] ⧸ Ideal.span {poly r.1.2})
            (Ideal.Quotient.field _) (Ideal.Quotient.field _)
            (AdjoinRoot.tensorSwapFactorQuotientEquiv (poly p) (poly h) q).toRingHom
            (monicIrreducibleResidue q.1.2 x)) := by
  classical
  let B : Gal(E/k) ≃ S :=
    (Equiv.ofBijective
      (fun σ : Gal(E/k) => AdjoinRoot.towerFactor (poly p) (poly h)
        (rationalSplitComp (poly p) (poly h) f σ))
      (AdjoinRoot.towerFactor_comp_gal_bijective (poly p) (poly h) f (monic p))).trans
        (Equiv.subtypeEquivRight hS).symm
  rw [monicIrreducibleResidue_milnorKNormRing_ratFunc_eq_sum_gal_of_split p hsep hp h f]
  simp only [Finset.attach_eq_univ]
  refine Fintype.sum_equiv B _ _ ?_
  intro σ
  let g := rationalSplitComp (poly p) (poly h) f σ
  let q := AdjoinRoot.towerFactor (poly p) (poly h) g
  let r := AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h) q
  change milnorKRingMap
      (AdjoinRoot.towerFactorRingEquiv (poly p) (poly h) g).toRingHom
      (monicIrreducibleResidue q.1.2 x) =
    simpleMilnorNorm r.1.2
      (milnorKRingMap
        (AdjoinRoot.tensorSwapFactorQuotientEquiv (poly p) (poly h) q).toRingHom
        (monicIrreducibleResidue q.1.2 x))
  rw [rationalSplit_simpleNorm_degree_one r.1.2
    (AdjoinRoot.towerFactor_matched_natDegree (poly p) (poly h) g)
    (AdjoinRoot.towerFactorTargetEquiv (poly p) (poly h) g)]
  exact (milnorKRingMap_comp_apply
    (AdjoinRoot.tensorSwapFactorQuotientEquiv (poly p) (poly h) q).toRingHom
    (AdjoinRoot.towerFactorTargetEquiv (poly p) (poly h) g).toRingHom
    (monicIrreducibleResidue q.1.2 x)).symm

end Stacks.Chow
