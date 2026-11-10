/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.FieldTheory.AdjoinRoot.RationalCoefficient
public import Colib.RingTheory.AdjoinRoot.OriginToPowerSeries
public import StacksFrontier.RingTheory.AdjoinRoot.FractionRing

/-!
# The actual generic-field square above the root-field origin

The original map from the origin local ring of `AdjoinRoot p` to the constant
power-series root algebra agrees in its actual Laurent root field with the
original rational coefficient equivalence followed by `AdjoinRoot.map`.
Both field maps and both local rings are the existing ones. The square is
proved on the original polynomial constants and coordinate and then on the
actual localization, in arbitrary characteristic and without normality or
degree assumptions.

The coefficient calculation uses the existing polynomial-to-rational-to-Laurent
scalar tower. It does not introduce a scalar tower for the distinct native
actions along `k`, `RatFunc k`, and `LaurentSeries k`.
-/

@[expose] public noncomputable section

open Polynomial Stacks.Chow
open scoped RatFunc
attribute [local instance] Polynomial.algebra

namespace RatFunc

variable {k : Type*} [Field k]

/-- The actual rational-to-Laurent map preserves the native constant inclusion. -/
theorem algebraMap_laurentSeries_comp_C :
    (algebraMap (RatFunc k) (LaurentSeries k)).comp (RatFunc.C : k →+* RatFunc k) =
      algebraMap k (LaurentSeries k) := by
  apply RingHom.ext
  intro a
  change algebraMap (RatFunc k) (LaurentSeries k) (RatFunc.C a) =
    HahnSeries.ofPowerSeries ℤ k (PowerSeries.C a)
  rw [← RatFunc.algebraMap_C,
    ← IsScalarTower.algebraMap_apply k[X] (RatFunc k) (LaurentSeries k)]
  change HahnSeries.ofPowerSeries ℤ k ((Polynomial.C a : k[X]) : PowerSeries k) =
    HahnSeries.ofPowerSeries ℤ k (PowerSeries.C a)
  rw [Polynomial.coe_C]

end RatFunc

namespace AdjoinRoot

variable {k : Type*} [Field k] (p : k[X]) [Fact (Irreducible p)]

/-- The inverse rational coefficient comparison preserves the original base
coordinate, as a coefficient of the actual mapped root algebra. -/
theorem rationalCoefficientAlgEquiv_symm_X (hp : p.Monic) :
    (rationalCoefficientAlgEquiv p hp).symm (RatFunc.X : RatFunc (AdjoinRoot p)) =
      of (p.map (RatFunc.C : k →+* RatFunc k)) (RatFunc.X : RatFunc k) := by
  have hX : algebraMap (RatFunc k) (RatFunc (AdjoinRoot p))
      (RatFunc.X : RatFunc k) = RatFunc.X := by
    rw [RatFunc.algebraMap_eq_mapRingHom]
    change RatFunc.mapRingHom _ _ (algebraMap k[X] (RatFunc k) X) = _
    rw [RatFunc.mapRingHom_algebraMap]
    change algebraMap (AdjoinRoot p)[X] (RatFunc (AdjoinRoot p))
      ((X : k[X]).map (algebraMap k (AdjoinRoot p))) = _
    rw [Polynomial.map_X, RatFunc.algebraMap_X]
  calc
    _ = (rationalCoefficientAlgEquiv p hp).symm
        (algebraMap (RatFunc k) (RatFunc (AdjoinRoot p)) (RatFunc.X : RatFunc k)) :=
      congrArg (rationalCoefficientAlgEquiv p hp).symm hX.symm
    _ = _ := (rationalCoefficientAlgEquiv p hp).symm.commutes RatFunc.X

variable [Fact p.Monic]

/-- The actual upper rational-to-Laurent root map and the native fraction map
commute with the original origin-localization map to the power-series root algebra. -/
theorem originToPowerSeries_generic_square :
    (RingHom.comp
      (map (algebraMap (RatFunc k) (LaurentSeries k))
        (p.map (RatFunc.C : k →+* RatFunc k))
        (p.map (algebraMap k (LaurentSeries k))) (by
          rw [Polynomial.map_map, RatFunc.algebraMap_laurentSeries_comp_C]))
      (rationalCoefficientAlgEquiv p (Fact.out : p.Monic)).symm.toRingHom).comp
        (algebraMap (localRingAtOrigin (AdjoinRoot p)) (RatFunc (AdjoinRoot p))) =
      (Stacks.AdjoinRootFraction.toMapAdjoinRoot (LaurentSeries k)
        (p := p.map (PowerSeries.C : k →+* PowerSeries k))
        (q := p.map (algebraMap k (LaurentSeries k))) (by
          rw [Polynomial.map_map]
          rfl)).comp (originToPowerSeries p) := by
  let f := map (algebraMap (RatFunc k) (LaurentSeries k))
    (p.map (RatFunc.C : k →+* RatFunc k))
    (p.map (algebraMap k (LaurentSeries k))) (by
      rw [Polynomial.map_map, RatFunc.algebraMap_laurentSeries_comp_C])
  let g := Stacks.AdjoinRootFraction.toMapAdjoinRoot (LaurentSeries k)
    (p := p.map (PowerSeries.C : k →+* PowerSeries k))
    (q := p.map (algebraMap k (LaurentSeries k))) (by
      rw [Polynomial.map_map]
      rfl)
  let cRat := map (RatFunc.C : k →+* RatFunc k) p (p.map RatFunc.C) dvd_rfl
  let cSeries := map (PowerSeries.C : k →+* PowerSeries k) p
    (p.map PowerSeries.C) dvd_rfl
  have hconstants : f.comp cRat = g.comp cSeries := by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro a
      simp only [RingHom.comp_apply, f, g, cRat, cSeries, map_of,
        Stacks.AdjoinRootFraction.toMapAdjoinRoot_of]
      change of (p.map (algebraMap k (LaurentSeries k)))
          (algebraMap (RatFunc k) (LaurentSeries k) (RatFunc.C a)) =
        of (p.map (algebraMap k (LaurentSeries k)))
          (algebraMap k (LaurentSeries k) a)
      exact congrArg (of (p.map (algebraMap k (LaurentSeries k))))
        (RingHom.congr_fun RatFunc.algebraMap_laurentSeries_comp_C a)
    · simp only [RingHom.comp_apply, f, g, cRat, cSeries, map_root,
        Stacks.AdjoinRootFraction.toMapAdjoinRoot_root]
  change (f.comp (rationalCoefficientAlgEquiv p (Fact.out : p.Monic)).symm.toRingHom).comp
      (algebraMap (localRingAtOrigin (AdjoinRoot p)) (RatFunc (AdjoinRoot p))) =
    g.comp (originToPowerSeries p)
  apply IsLocalization.ringHom_ext
    (Ideal.span ({X} : Set (AdjoinRoot p)[X])).primeCompl
  apply Polynomial.ringHom_ext
  · intro x
    change f ((rationalCoefficientAlgEquiv p (Fact.out : p.Monic)).symm
        (algebraMap (localRingAtOrigin (AdjoinRoot p)) (RatFunc (AdjoinRoot p))
          (algebraMap (AdjoinRoot p)[X] (localRingAtOrigin (AdjoinRoot p)) (C x)))) =
      g (originToPowerSeries p
        (algebraMap (AdjoinRoot p)[X] (localRingAtOrigin (AdjoinRoot p)) (C x)))
    rw [← IsScalarTower.algebraMap_apply (AdjoinRoot p)[X]
        (localRingAtOrigin (AdjoinRoot p)) (RatFunc (AdjoinRoot p)),
      RatFunc.algebraMap_C, rationalCoefficientAlgEquiv_symm_C,
      originToPowerSeries_algebraMap, Polynomial.eval₂_C]
    exact RingHom.congr_fun hconstants x
  · change f ((rationalCoefficientAlgEquiv p (Fact.out : p.Monic)).symm
        (algebraMap (localRingAtOrigin (AdjoinRoot p)) (RatFunc (AdjoinRoot p))
          (algebraMap (AdjoinRoot p)[X] (localRingAtOrigin (AdjoinRoot p)) X))) =
      g (originToPowerSeries p
        (algebraMap (AdjoinRoot p)[X] (localRingAtOrigin (AdjoinRoot p)) X))
    rw [← IsScalarTower.algebraMap_apply (AdjoinRoot p)[X]
        (localRingAtOrigin (AdjoinRoot p)) (RatFunc (AdjoinRoot p)),
      RatFunc.algebraMap_X, rationalCoefficientAlgEquiv_symm_X, originToPowerSeries_X]
    dsimp only [f, g]
    rw [map_of, Stacks.AdjoinRootFraction.toMapAdjoinRoot_of]
    change of (p.map (algebraMap k (LaurentSeries k)))
        (((RatFunc.X : RatFunc k) : LaurentSeries k)) =
      of (p.map (algebraMap k (LaurentSeries k)))
        (((PowerSeries.X : PowerSeries k) : LaurentSeries k))
    rw [RatFunc.coe_X, PowerSeries.coe_X]

/-- On every original polynomial, the actual upper generic map is its original
power-series evaluation followed by the native fraction map. -/
theorem originToPowerSeries_generic_square_polynomial (q : (AdjoinRoot p)[X]) :
    (RingHom.comp
      (map (algebraMap (RatFunc k) (LaurentSeries k))
        (p.map (RatFunc.C : k →+* RatFunc k))
        (p.map (algebraMap k (LaurentSeries k))) (by
          rw [Polynomial.map_map, RatFunc.algebraMap_laurentSeries_comp_C]))
      (rationalCoefficientAlgEquiv p (Fact.out : p.Monic)).symm.toRingHom)
        (algebraMap (AdjoinRoot p)[X] (RatFunc (AdjoinRoot p)) q) =
      Stacks.AdjoinRootFraction.toMapAdjoinRoot (LaurentSeries k)
        (p := p.map (PowerSeries.C : k →+* PowerSeries k))
        (q := p.map (algebraMap k (LaurentSeries k))) (by
          rw [Polynomial.map_map]
          rfl)
        (q.eval₂ (map (PowerSeries.C : k →+* PowerSeries k) p
          (p.map PowerSeries.C) dvd_rfl) (of _ PowerSeries.X)) := by
  have h := RingHom.congr_fun (originToPowerSeries_generic_square p)
    (algebraMap (AdjoinRoot p)[X] (localRingAtOrigin (AdjoinRoot p)) q)
  simpa only [RingHom.comp_apply,
    ← IsScalarTower.algebraMap_apply (AdjoinRoot p)[X]
      (localRingAtOrigin (AdjoinRoot p)) (RatFunc (AdjoinRoot p)),
    originToPowerSeries_algebraMap] using h

end AdjoinRoot
