/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdjoinRoot.OriginGenericSquare
public import Colib.RingTheory.KTheory.MilnorK.Norm.RationalConstant
public import Colib.AlgebraicGeometry.ProjectiveLine.ChartInversionMap
public import Colib.FieldTheory.AdjoinRoot.PurelyInseparable
public import Colib.RingTheory.KTheory.MilnorK.Norm.PurePrimeEquivariance
public import Colib.FieldTheory.RatFunc.PurelyInseparable

/-!
# The rational chosen norm in purely inseparable prime degree

The original rational norm commutes with the literal coefficient and root
map to the Laurent completion. The actual rational coefficient map also
intertwines chart inversion on the two fields.
-/

@[expose] public noncomputable section

open Polynomial Module
open scoped RatFunc
attribute [local instance] Polynomial.algebra Ideal.Quotient.field

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

variable {k : Type u} [Field k] {d : ℕ}

local instance rationalPure_factIrreducible (p : MonicIrreducibleOfDegree k d) :
    Fact (Irreducible (poly p)) := ⟨irreducible p⟩

local instance rationalPure_factLaurentIrreducible (p : MonicIrreducibleOfDegree k d) :
    Fact (Irreducible ((poly p).map (algebraMap k (LaurentSeries k)))) :=
  ⟨(monic p).irreducible_map_laurentSeries_C (irreducible p)⟩

local instance rationalPure_finiteRoot (p : MonicIrreducibleOfDegree k d) :
    Module.Finite k (AdjoinRoot (poly p)) := (monic p).finite_adjoinRoot

local instance rationalPure_finiteRatFuncRoot (p : MonicIrreducibleOfDegree k d) :
    Module.Finite (RatFunc k) (RatFunc (AdjoinRoot (poly p))) :=
  FiniteDimensional.of_finrank_pos (by
    rw [AdjoinRoot.finrank_ratFunc_adjoinRoot]
    exact (irreducible p).natDegree_pos)

local instance rationalPure_finiteLaurentRoot (p : MonicIrreducibleOfDegree k d) :
    Module.Finite (LaurentSeries k)
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) :=
  ((monic p).map _).finite_adjoinRoot

variable (p : MonicIrreducibleOfDegree k d)

/-- The literal coefficient and root map in the original origin square. -/
abbrev ratFuncToLaurentRoot :
    RatFunc (AdjoinRoot (poly p)) →+*
      AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k))) :=
  (AdjoinRoot.map (algebraMap (RatFunc k) (LaurentSeries k))
    (poly p.ratFunc) ((poly p).map (algebraMap k (LaurentSeries k))) (by
      change (poly p).map (algebraMap k (LaurentSeries k)) ∣
        ((poly p).map (RatFunc.C : k →+* RatFunc k)).map
          (algebraMap (RatFunc k) (LaurentSeries k))
      rw [Polynomial.map_map, RatFunc.algebraMap_laurentSeries_comp_C])).comp
    (AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p)).symm.toRingHom

variable [IsPurelyInseparable k (AdjoinRoot (poly p))]

/-- The chosen norm commutes with restriction to the literal Laurent root field. -/
theorem milnorKNormRing_ratFunc_map_laurentSeries_of_isPurelyInseparable (hp : d.Prime)
    (x : MilnorKRing (RatFunc (AdjoinRoot (poly p)))) :
    milnorKRingMap (algebraMap (RatFunc k) (LaurentSeries k))
        (milnorKNormRing (RatFunc k) (RatFunc (AdjoinRoot (poly p))) x) =
      milnorKNormRing (LaurentSeries k)
        (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k))))
        (milnorKRingMap (ratFuncToLaurentRoot p) x) := by
  let : Fact (Irreducible ((poly p).map (RatFunc.C : k →+* RatFunc k))) :=
    ⟨(monic p).irreducible_map_ratFunc_C (irreducible p)⟩
  let q : MonicIrreducibleOfDegree (LaurentSeries k) d :=
    ⟨(poly p).map (algebraMap k (LaurentSeries k)), (monic p).map _,
      (monic p).irreducible_map_laurentSeries_C (irreducible p),
      (Polynomial.natDegree_map _).trans (natDegree_eq p)⟩
  have hq : poly q = (poly p.ratFunc).map (algebraMap (RatFunc k) (LaurentSeries k)) := by
    change (poly p).map (algebraMap k (LaurentSeries k)) =
      ((poly p).map (RatFunc.C : k →+* RatFunc k)).map
        (algebraMap (RatFunc k) (LaurentSeries k))
    rw [Polynomial.map_map, RatFunc.algebraMap_laurentSeries_comp_C]
  let : IsPurelyInseparable (RatFunc k) (RatFunc (AdjoinRoot (poly p))) :=
    RatFunc.isPurelyInseparable_ratFunc
  let : IsPurelyInseparable (LaurentSeries k)
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) :=
    AdjoinRoot.isPurelyInseparable_map_of_isPurelyInseparable
  have hpRat : Nat.Prime (finrank (RatFunc k) (RatFunc (AdjoinRoot (poly p)))) := by
    rw [AdjoinRoot.finrank_ratFunc_adjoinRoot, natDegree_eq]
    exact hp
  have hpLaurent : Nat.Prime (finrank (LaurentSeries k)
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k))))) := by
    rw [AdjoinRoot.finrank_eq_natDegree ((monic p).map _), Polynomial.natDegree_map, natDegree_eq]
    exact hp
  let e : AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k))) ≃ₐ[LaurentSeries k]
      ((LaurentSeries k)[X] ⧸ Ideal.span {poly q}) :=
    { toRingEquiv := RingEquiv.refl _, commutes' := fun _ => rfl }
  have hchosen (y : MilnorKRing
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k))))) :
      milnorKNormRing (LaurentSeries k)
        (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) y = simpleMilnorNorm q y := by
    rw [milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_prime_of_isPurelyInseparable
      hpLaurent q e y]
    exact congrArg (simpleMilnorNorm q) (milnorKRingMap_id_apply y)
  let eRat := (AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p)).symm
  let f := AdjoinRoot.map (algebraMap (RatFunc k) (LaurentSeries k))
    (poly p.ratFunc) (poly q) (hq ▸ dvd_rfl)
  rw [milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_prime_of_isPurelyInseparable
      hpRat p.ratFunc eRat x,
    simpleMilnorNorm_map_of_poly_eq_map (algebraMap (RatFunc k) (LaurentSeries k))
      p.ratFunc q hq, hchosen]
  exact congrArg (simpleMilnorNorm q) (milnorKRingMap_comp_apply eRat.toRingHom f x)

/-- The same norm restriction on each original homogeneous group. -/
theorem milnorKNorm_ratFunc_map_laurentSeries_of_isPurelyInseparable (hp : d.Prime) (n : ℕ)
    (x : MilnorKTheory (RatFunc (AdjoinRoot (poly p))) n) :
    milnorKTheoryMap (algebraMap (RatFunc k) (LaurentSeries k)) n
        (milnorKNorm (RatFunc k) (RatFunc (AdjoinRoot (poly p))) n x) =
      milnorKNorm (LaurentSeries k)
        (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k))))
        n (milnorKTheoryMap (ratFuncToLaurentRoot p) n x) := by
  simp only [milnorKTheoryMap_eq_transport]
  apply Subtype.ext
  exact milnorKNormRing_ratFunc_map_laurentSeries_of_isPurelyInseparable p hp (x : MilnorKRing _)

/-- The original chosen rational norm commutes with the actual chart inversion. -/
theorem milnorKNorm_ratFunc_map_chartInversion_of_isPurelyInseparable (hp : d.Prime) (n : ℕ)
    (x : MilnorKTheory (RatFunc (AdjoinRoot (poly p))) n) :
    milnorKNorm (RatFunc k) (RatFunc (AdjoinRoot (poly p))) n
        (milnorKTheoryMap
          (AlgebraicGeometry.projectiveLineChartInversion (AdjoinRoot (poly p))).toRingHom n x) =
      milnorKTheoryMap (AlgebraicGeometry.projectiveLineChartInversion k).toRingHom n
        (milnorKNorm (RatFunc k) (RatFunc (AdjoinRoot (poly p))) n x) := by
  let : IsPurelyInseparable (RatFunc k) (RatFunc (AdjoinRoot (poly p))) :=
    RatFunc.isPurelyInseparable_ratFunc
  have hpRat : Nat.Prime (finrank (RatFunc k) (RatFunc (AdjoinRoot (poly p)))) := by
    rw [AdjoinRoot.finrank_ratFunc_adjoinRoot, natDegree_eq]
    exact hp
  have hcomm :=
    AlgebraicGeometry.projectiveLineChartInversion_comp_mapRingHom
      (algebraMap k (AdjoinRoot (poly p)))
  rw [← RatFunc.algebraMap_eq_mapRingHom] at hcomm
  simp only [milnorKTheoryMap_eq_transport]
  exact (milnorKNorm_map_ringEquiv_of_prime_of_isPurelyInseparable hpRat
    (AlgebraicGeometry.projectiveLineChartInversion k)
    (AlgebraicGeometry.projectiveLineChartInversion (AdjoinRoot (poly p))) hcomm n x).symm

end Stacks.Chow

end
