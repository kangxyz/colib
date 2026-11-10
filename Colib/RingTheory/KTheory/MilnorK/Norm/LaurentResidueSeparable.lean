/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.LaurentUnramified
public import Colib.RingTheory.KTheory.MilnorK.Norm.NormalPrimeChosenComparisonSeparable
public import Colib.RingTheory.KTheory.MilnorK.Norm.PresentationSupport
public import Colib.FieldTheory.AdjoinRoot.NormalScalar

/-!
# Returning the actual Laurent residue norm to the original constant fields

For a separable normal prime-degree constant extension in any characteristic,
the original chosen residue norm is identified with the original chosen
constant-field norm through the established power-series residue equivalences.
The proof preserves both literal coefficient squares and uses the existing
finite-separable normal-prime chosen/simple comparison.

The existing mixed, K1 and quadratic Laurent squares consequently return to
the original constant fields. No higher-prime all-symbol square is claimed.
No norm, residue field, generic field, or structure map is replaced.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing Module

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

attribute [local instance]
  Stacks.Chow.laurentUnramified_factMonic
  Stacks.Chow.laurentUnramified_factIrreducible
  Stacks.Chow.laurentUnramified_factIrreducibleLaurent
  Stacks.Chow.laurentUnramified_isDomain
  Stacks.Chow.laurentUnramified_isLocalRing
  Stacks.Chow.laurentUnramified_isDiscreteValuationRing
  Stacks.Chow.laurentUnramified_finitePowerSeries
  Stacks.Chow.laurentUnramified_torsionFreePowerSeries
  Stacks.Chow.laurentUnramified_isLocalHom
  Stacks.Chow.laurentUnramifiedAlgebra
  Stacks.Chow.laurentUnramified_isScalarTower
  Stacks.Chow.laurentUnramified_isFractionRing
  Stacks.Chow.laurentUnramified_finiteConstant
  Stacks.Chow.laurentUnramified_finiteLaurent

variable {k : Type u} [Field k] {d : ℕ} (p : MonicIrreducibleOfDegree k d)
  [Normal k (AdjoinRoot (poly p))]

/-- The actual chosen residue norm becomes the original chosen constant-field
norm under the existing power-series residue equivalences. -/
theorem milnorKNormRing_powerSeriesResidueEquiv_of_separable
    (hsep : (poly p).Separable) (hp : d.Prime)
    (y : MilnorKRing
      (ResidueField (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k))))) :
    milnorKRingMap PowerSeries.residueFieldOfPowerSeries.toRingHom
        (milnorKNormRing (ResidueField (PowerSeries k))
          (ResidueField (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))) y) =
      milnorKNormRing k (AdjoinRoot (poly p))
        (milnorKRingMap (AdjoinRoot.powerSeriesResidueEquiv (poly p)).toRingHom y) := by
  let : Algebra.IsSeparable k (AdjoinRoot (poly p)) :=
    isSeparable_powerSeriesRoot_constant p hsep
  let : Algebra.IsSeparable (ResidueField (PowerSeries k))
      (ResidueField (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))) :=
    isSeparable_powerSeriesRoot_residue p hsep
  let q : MonicIrreducibleOfDegree (ResidueField (PowerSeries k)) d :=
    ⟨((poly p).map (PowerSeries.C : k →+* PowerSeries k)).map (residue (PowerSeries k)),
      ((monic p).map _).map _,
      (monic p).irreducible_map_powerSeries_C_residue (irreducible p), by
        rw [((monic p).map _).natDegree_map, (monic p).natDegree_map, natDegree_eq p]⟩
  let : Fact (Irreducible (poly q)) := ⟨irreducible q⟩
  let e :
      ResidueField (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k))) ≃ₐ[
        ResidueField (PowerSeries k)]
      ((ResidueField (PowerSeries k))[X] ⧸ Ideal.span {poly q}) :=
    { toRingEquiv := AdjoinRoot.residueFieldEquivAdjoinRoot
        ((poly p).map (PowerSeries.C : k →+* PowerSeries k)) (irreducible q)
      commutes' := by
        intro a
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
        change AdjoinRoot.residueFieldEquivAdjoinRoot
            ((poly p).map (PowerSeries.C : k →+* PowerSeries k)) (irreducible q)
            (residue _ (AdjoinRoot.of _ b)) =
          AdjoinRoot.of (poly q) (residue (PowerSeries k) b)
        exact AdjoinRoot.residueFieldEquivAdjoinRoot_residue_of _ (irreducible q) b }
  have hqκ : poly q = (poly p).map (algebraMap k (ResidueField (PowerSeries k))) := by
    change ((poly p).map (PowerSeries.C : k →+* PowerSeries k)).map
      (residue (PowerSeries k)) = _
    rw [Polynomial.map_map]
    rfl
  let : IsSplittingField (ResidueField (PowerSeries k)) (AdjoinRoot (poly q))
      ((poly p).map (algebraMap k (ResidueField (PowerSeries k)))) :=
    AdjoinRoot.isSplittingField_of_dvd_map (monic p) (hqκ ▸ dvd_rfl)
  let : Normal (ResidueField (PowerSeries k)) (AdjoinRoot (poly q)) :=
    Normal.of_isSplittingField
      ((poly p).map (algebraMap k (ResidueField (PowerSeries k))))
  let e_q : AdjoinRoot (poly q) ≃ₐ[ResidueField (PowerSeries k)]
      ((ResidueField (PowerSeries k))[X] ⧸ Ideal.span {poly q}) :=
    { toRingEquiv := RingEquiv.refl _
      commutes' := fun _ => rfl }
  let : Normal (ResidueField (PowerSeries k))
      ((ResidueField (PowerSeries k))[X] ⧸ Ideal.span {poly q}) :=
    Normal.of_algEquiv e_q
  let : Normal (ResidueField (PowerSeries k))
      (ResidueField (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))) :=
    Normal.of_algEquiv e.symm
  have hdegree :
      finrank (ResidueField (PowerSeries k))
        (ResidueField (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))) = d := by
    rw [AdjoinRoot.finrank_residueField_eq_natDegree ((monic p).map _)
      ((monic p).irreducible_map_powerSeries_C_residue (irreducible p)) (by
        rw [(monic p).natDegree_map]
        exact (irreducible p).natDegree_pos), (monic p).natDegree_map, natDegree_eq p]
  have hprime : Nat.Prime
      (finrank (ResidueField (PowerSeries k))
        (ResidueField (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k))))) := by
    rw [hdegree]
    exact hp
  have hq : poly p = (poly q).map PowerSeries.residueFieldOfPowerSeries.toRingHom :=
    (Polynomial.map_powerSeries_C_residueFieldOfPowerSeries (poly p)).symm
  let g : ((ResidueField (PowerSeries k))[X] ⧸ Ideal.span {poly q}) →+*
      (k[X] ⧸ Ideal.span {poly p}) :=
    AdjoinRoot.map PowerSeries.residueFieldOfPowerSeries.toRingHom
      (poly q) (poly p) (hq ▸ dvd_rfl)
  have hcomp : g.comp e.toRingHom =
      (AdjoinRoot.powerSeriesResidueEquiv (poly p)).toRingHom := by
    apply RingHom.ext
    intro z
    rfl
  let e₀ : AdjoinRoot (poly p) ≃ₐ[k] (k[X] ⧸ Ideal.span {poly p}) :=
    { toRingEquiv := RingEquiv.refl _
      commutes' := fun _ => rfl }
  have hprime₀ : Nat.Prime (finrank k (AdjoinRoot (poly p))) := by
    rw [AdjoinRoot.finrank_eq_natDegree (monic p), natDegree_eq p]
    exact hp
  have hchosen (z : MilnorKRing (AdjoinRoot (poly p))) :
      milnorKNormRing k (AdjoinRoot (poly p)) z = simpleMilnorNorm p z := by
    calc
      _ = simpleMilnorNorm p (milnorKRingMap e₀.toRingHom z) :=
        milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_normal_prime_of_separable hprime₀ p e₀ z
      _ = _ := congrArg (simpleMilnorNorm p)
        (show milnorKRingMap e₀.toRingHom z = z from milnorKRingMap_id_apply z)
  calc
    _ = milnorKRingMap PowerSeries.residueFieldOfPowerSeries.toRingHom
        (simpleMilnorNorm q (milnorKRingMap e.toRingHom y)) :=
      congrArg (milnorKRingMap PowerSeries.residueFieldOfPowerSeries.toRingHom)
        (milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_normal_prime_of_separable hprime q e y)
    _ = simpleMilnorNorm p (milnorKRingMap g (milnorKRingMap e.toRingHom y)) :=
      simpleMilnorNorm_map_of_poly_eq_map
        PowerSeries.residueFieldOfPowerSeries.toRingHom q p hq _
    _ = simpleMilnorNorm p (milnorKRingMap (g.comp e.toRingHom) y) :=
      congrArg (simpleMilnorNorm p) (milnorKRingMap_comp_apply e.toRingHom g y)
    _ = simpleMilnorNorm p
        (milnorKRingMap (AdjoinRoot.powerSeriesResidueEquiv (poly p)).toRingHom y) :=
      congrArg (fun f :
        ResidueField (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k))) →+*
          (k[X] ⧸ Ideal.span {poly p}) => simpleMilnorNorm p (milnorKRingMap f y)) hcomp
    _ = _ := (hchosen _).symm

/-- The actual residue chosen-norm comparison in every homogeneous degree. -/
theorem milnorKNorm_powerSeriesResidueEquiv_of_separable
    (hsep : (poly p).Separable) (hp : d.Prime) (n : ℕ)
    (y : MilnorKTheory
      (ResidueField (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))) n) :
    milnorKTheoryMap PowerSeries.residueFieldOfPowerSeries.toRingHom n
        (milnorKNorm (ResidueField (PowerSeries k))
          (ResidueField (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))) n y) =
      milnorKNorm k (AdjoinRoot (poly p)) n
        (milnorKTheoryMap (AdjoinRoot.powerSeriesResidueEquiv (poly p)).toRingHom n y) := by
  simp only [milnorKTheoryMap_eq_transport]
  apply Subtype.ext
  exact milnorKNormRing_powerSeriesResidueEquiv_of_separable p hsep hp (y : MilnorKRing _)

/-- On the original mixed span, the actual Laurent chosen norm-residue square
returns to the original constant fields in arbitrary characteristic. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_laurentSeries_to_constants_of_mem_mixedSpan
    (hsep : (poly p).Separable) (hp : d.Prime) (m : ℕ)
    (x : MilnorKTheory
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) (m + 1))
    (hx : x ∈ milnorKMixedSpan (algebraMap (LaurentSeries k)
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k))))) m) :
    milnorKTheoryMap PowerSeries.residueFieldOfPowerSeries.toRingHom m
        (dvrMilnorTameSymbol' (PowerSeries k) (LaurentSeries k) m
          (milnorKNorm (LaurentSeries k)
            (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) (m + 1) x)) =
      milnorKNorm k (AdjoinRoot (poly p)) m
        (milnorKTheoryMap (AdjoinRoot.powerSeriesResidueEquiv (poly p)).toRingHom m
          (dvrMilnorTameSymbol'
            (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
            (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) m x)) := by
  have hmono := dvrMilnorTameSymbol'_milnorKNorm_laurentSeries_of_mem_mixedSpan p m x hx
  calc
    _ = milnorKTheoryMap PowerSeries.residueFieldOfPowerSeries.toRingHom m
        (milnorKNorm (ResidueField (PowerSeries k))
          (ResidueField (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))) m
          (dvrMilnorTameSymbol'
            (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
            (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) m x)) :=
      congrArg (milnorKTheoryMap PowerSeries.residueFieldOfPowerSeries.toRingHom m) hmono
    _ = _ := milnorKNorm_powerSeriesResidueEquiv_of_separable p hsep hp m _

/-- Every Laurent class satisfies the square returned to original constants
for a separable normal quadratic constant extension, in arbitrary characteristic. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_laurentSeries_to_constants_of_degree_le_two
    (hsep : (poly p).Separable) (hp : d.Prime) (hd : d ≤ 2) (m : ℕ)
    (x : MilnorKTheory
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) (m + 1)) :
    milnorKTheoryMap PowerSeries.residueFieldOfPowerSeries.toRingHom m
        (dvrMilnorTameSymbol' (PowerSeries k) (LaurentSeries k) m
          (milnorKNorm (LaurentSeries k)
            (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) (m + 1) x)) =
      milnorKNorm k (AdjoinRoot (poly p)) m
        (milnorKTheoryMap (AdjoinRoot.powerSeriesResidueEquiv (poly p)).toRingHom m
          (dvrMilnorTameSymbol'
            (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
            (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) m x)) := by
  have hmono := dvrMilnorTameSymbol'_milnorKNorm_laurentSeries_of_degree_le_two p hd m x
  calc
    _ = milnorKTheoryMap PowerSeries.residueFieldOfPowerSeries.toRingHom m
        (milnorKNorm (ResidueField (PowerSeries k))
          (ResidueField (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))) m
          (dvrMilnorTameSymbol'
            (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
            (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) m x)) :=
      congrArg (milnorKTheoryMap PowerSeries.residueFieldOfPowerSeries.toRingHom m) hmono
    _ = _ := milnorKNorm_powerSeriesResidueEquiv_of_separable p hsep hp m _

/-- The full K1 Laurent square returns to the original constant fields for
any separable normal prime-degree constant extension. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_laurentSeries_to_constants_degree_one
    (hsep : (poly p).Separable) (hp : d.Prime)
    (x : MilnorKTheory
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) 1) :
    milnorKTheoryMap PowerSeries.residueFieldOfPowerSeries.toRingHom 0
        (dvrMilnorTameSymbol' (PowerSeries k) (LaurentSeries k) 0
          (milnorKNorm (LaurentSeries k)
            (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) 1 x)) =
      milnorKNorm k (AdjoinRoot (poly p)) 0
        (milnorKTheoryMap (AdjoinRoot.powerSeriesResidueEquiv (poly p)).toRingHom 0
          (dvrMilnorTameSymbol'
            (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
            (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) 0 x)) := by
  have hmono := dvrMilnorTameSymbol'_milnorKNorm_laurentSeries_degree_one p x
  calc
    _ = milnorKTheoryMap PowerSeries.residueFieldOfPowerSeries.toRingHom 0
        (milnorKNorm (ResidueField (PowerSeries k))
          (ResidueField (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))) 0
          (dvrMilnorTameSymbol'
            (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
            (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) 0 x)) :=
      congrArg (milnorKTheoryMap PowerSeries.residueFieldOfPowerSeries.toRingHom 0) hmono
    _ = _ := milnorKNorm_powerSeriesResidueEquiv_of_separable p hsep hp 0 _

end Stacks.Chow
