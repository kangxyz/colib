/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.MonicResiduePrime
public import Colib.RingTheory.KTheory.MilnorK.Norm.NormalPrimeChosenComparison
public import Colib.RingTheory.KTheory.MilnorK.Norm.PresentationSupport
public import Colib.RingTheory.AdjoinRoot.PowerSeriesResidue
public import Colib.FieldTheory.AdjoinRoot.NormalScalar

/-!
# The actual complete-local norm-residue square in normal prime degree

For the original normal prime-degree root field over a characteristic-zero field,
the chosen norm on the literal Laurent constant root field commutes with the
actual DVR residue. Both residue fields are returned to the original constant
fields through their existing native equivalences.

The chosen residue norm is compared with its actual polynomial presentation,
then the literal residue polynomial is mapped to the original polynomial by the
native simple-norm coefficient theorem. The generic field is always the root
field of the single polynomial mapped directly to LaurentSeries. Its structure
map from the power-series root algebra is the native toMapAdjoinRoot with the
proved equality of the literal and iterated coefficient polynomials.

No norm, residue carrier, scalar action, general presentation independence or
chosen-norm tower law is introduced.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing Module

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

variable {k : Type u} [Field k] {d : ℕ}

local instance (p : MonicIrreducibleOfDegree k d) : Fact (poly p).Monic :=
  ⟨monic p⟩

local instance laurentResidueFactIrreducible
    (p : MonicIrreducibleOfDegree k d) : Fact (Irreducible (poly p)) :=
  ⟨irreducible p⟩

local instance (p : MonicIrreducibleOfDegree k d) :
    Fact (Irreducible ((poly p).map (algebraMap k (LaurentSeries k)))) :=
  ⟨(monic p).irreducible_map_laurentSeries_C (irreducible p)⟩

local instance (p : MonicIrreducibleOfDegree k d) :
    IsDomain (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k))) :=
  AdjoinRoot.isDomain_of_irreducible_map_residue ((monic p).map _)
    ((monic p).irreducible_map_powerSeries_C_residue (irreducible p))

local instance (p : MonicIrreducibleOfDegree k d) :
    IsLocalRing (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k))) :=
  AdjoinRoot.isLocalRing_of_irreducible_map_residue ((monic p).map _)
    ((monic p).irreducible_map_powerSeries_C_residue (irreducible p))

local instance (p : MonicIrreducibleOfDegree k d) :
    IsDiscreteValuationRing
      (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k))) := by
  apply AdjoinRoot.isDiscreteValuationRing ((monic p).map _)
    ((monic p).irreducible_map_powerSeries_C_residue (irreducible p))
  rw [(monic p).natDegree_map]
  exact (irreducible p).natDegree_pos

local instance (p : MonicIrreducibleOfDegree k d) :
    Module.Finite (PowerSeries k)
      (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k))) :=
  ((monic p).map _).finite_adjoinRoot

local instance (p : MonicIrreducibleOfDegree k d) :
    Module.IsTorsionFree (PowerSeries k)
      (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k))) := by
  apply AdjoinRoot.isTorsionFree_of_prime_of_degree_ne_zero
    (AdjoinRoot.prime_of_irreducible_map_residue ((monic p).map _)
      ((monic p).irreducible_map_powerSeries_C_residue (irreducible p)))
  apply ne_of_gt
  apply natDegree_pos_iff_degree_pos.mp
  rw [(monic p).natDegree_map]
  exact (irreducible p).natDegree_pos

local instance (p : MonicIrreducibleOfDegree k d) : IsLocalHom
    (algebraMap (PowerSeries k)
      (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))) := by
  rw [AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.isLocalHom_of_monic ((monic p).map _)

/-- The native algebra from the power series root extension to the Laurent series root field. -/
local instance laurentResiduePowerSeriesToLaurentRootAlgebra
    (p : MonicIrreducibleOfDegree k d) :
    Algebra (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) :=
  (Stacks.AdjoinRootFraction.toMapAdjoinRoot (LaurentSeries k)
    (p := (poly p).map (PowerSeries.C : k →+* PowerSeries k))
    (q := (poly p).map (algebraMap k (LaurentSeries k)))
    (by rw [Polynomial.map_map]; rfl)).toAlgebra

local instance (p : MonicIrreducibleOfDegree k d) :
    IsScalarTower (PowerSeries k)
      (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) := by
  apply IsScalarTower.of_algebraMap_eq
  intro a
  exact (Stacks.AdjoinRootFraction.toMapAdjoinRoot_of (LaurentSeries k)
    (p := (poly p).map (PowerSeries.C : k →+* PowerSeries k))
    (q := (poly p).map (algebraMap k (LaurentSeries k)))
    (by rw [Polynomial.map_map]; rfl) a).symm

local instance (p : MonicIrreducibleOfDegree k d) :
    IsFractionRing
      (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) :=
  Stacks.AdjoinRootFraction.isFractionRing_adjoinRoot (LaurentSeries k)
    (p := (poly p).map (PowerSeries.C : k →+* PowerSeries k))
    (q := (poly p).map (algebraMap k (LaurentSeries k)))
    (by rw [Polynomial.map_map]; rfl) (RingEquiv.refl _) ((monic p).map _)
    (by ext <;> rfl)

local instance laurentResidueFiniteConstant (p : MonicIrreducibleOfDegree k d) :
    Module.Finite k (AdjoinRoot (poly p)) := (monic p).finite_adjoinRoot

local instance (p : MonicIrreducibleOfDegree k d) :
    Module.Finite (LaurentSeries k)
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) :=
  ((monic p).map _).finite_adjoinRoot

variable [CharZero k] (p : MonicIrreducibleOfDegree k d)
  [Normal k (AdjoinRoot (poly p))]

local instance : CharZero (ResidueField (PowerSeries k)) :=
  RingHom.charZero PowerSeries.residueFieldOfPowerSeries.toRingHom

local instance : CharZero (LaurentSeries k) :=
  charZero_of_injective_algebraMap (algebraMap k (LaurentSeries k)).injective

/-- The actual chosen residue norm becomes the original chosen constant-field
norm under the existing power-series residue equivalences. -/
theorem milnorKNormRing_powerSeriesResidueEquiv (hp : d.Prime)
    (y : MilnorKRing
      (ResidueField (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k))))) :
    milnorKRingMap PowerSeries.residueFieldOfPowerSeries.toRingHom
        (milnorKNormRing (ResidueField (PowerSeries k))
          (ResidueField (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))) y) =
      milnorKNormRing k (AdjoinRoot (poly p))
        (milnorKRingMap (AdjoinRoot.powerSeriesResidueEquiv (poly p)).toRingHom y) := by
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
        milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_normal_prime hprime₀ p e₀ z
      _ = _ := congrArg (simpleMilnorNorm p)
        (show milnorKRingMap e₀.toRingHom z = z from milnorKRingMap_id_apply z)
  calc
    _ = milnorKRingMap PowerSeries.residueFieldOfPowerSeries.toRingHom
        (simpleMilnorNorm q (milnorKRingMap e.toRingHom y)) :=
      congrArg (milnorKRingMap PowerSeries.residueFieldOfPowerSeries.toRingHom)
        (milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_normal_prime hprime q e y)
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
theorem milnorKNorm_powerSeriesResidueEquiv (hp : d.Prime) (n : ℕ)
    (y : MilnorKTheory
      (ResidueField (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))) n) :
    milnorKTheoryMap PowerSeries.residueFieldOfPowerSeries.toRingHom n
        (milnorKNorm (ResidueField (PowerSeries k))
          (ResidueField (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))) n y) =
      milnorKNorm k (AdjoinRoot (poly p)) n
        (milnorKTheoryMap (AdjoinRoot.powerSeriesResidueEquiv (poly p)).toRingHom n y) := by
  simp only [milnorKTheoryMap_eq_transport]
  apply Subtype.ext
  exact milnorKNormRing_powerSeriesResidueEquiv p hp (y : MilnorKRing _)

/-- The chosen norm on the literal Laurent constant root field commutes with
the actual complete-local residue, returned to the original constant fields. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_laurentSeries (hp : d.Prime) (n : ℕ)
    (x : MilnorKTheory
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) (n + 1)) :
    milnorKTheoryMap PowerSeries.residueFieldOfPowerSeries.toRingHom n
        (dvrMilnorTameSymbol' (PowerSeries k) (LaurentSeries k) n
          (milnorKNorm (LaurentSeries k)
            (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) (n + 1) x)) =
      milnorKNorm k (AdjoinRoot (poly p)) n
        (milnorKTheoryMap (AdjoinRoot.powerSeriesResidueEquiv (poly p)).toRingHom n
          (dvrMilnorTameSymbol'
            (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
            (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) n x)) := by
  let : IsSplittingField (LaurentSeries k)
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k))))
      ((poly p).map (algebraMap k (LaurentSeries k))) :=
    AdjoinRoot.isSplittingField_of_dvd_map (monic p) dvd_rfl
  let : Normal (LaurentSeries k)
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) :=
    Normal.of_isSplittingField ((poly p).map (algebraMap k (LaurentSeries k)))
  let : IsGalois (LaurentSeries k)
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) :=
    { to_isSeparable := inferInstance, to_normal := inferInstance }
  have hprime : Nat.Prime (finrank (LaurentSeries k)
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k))))) := by
    rw [AdjoinRoot.finrank_eq_natDegree ((monic p).map _),
      (monic p).natDegree_map, natDegree_eq p]
    exact hp
  have hmono := dvrMilnorTameSymbol'_milnorKNorm_of_prime_galois_of_charZero
    (PowerSeries k)
    (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
    (LaurentSeries k)
    (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) hprime n x
  calc
    _ = milnorKTheoryMap PowerSeries.residueFieldOfPowerSeries.toRingHom n
        (milnorKNorm (ResidueField (PowerSeries k))
          (ResidueField (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))) n
          (dvrMilnorTameSymbol'
            (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
            (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) n x)) :=
      congrArg (milnorKTheoryMap PowerSeries.residueFieldOfPowerSeries.toRingHom n) hmono
    _ = _ := milnorKNorm_powerSeriesResidueEquiv p hp n _

end Stacks.Chow
