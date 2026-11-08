/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.FieldTheory.AdjoinRoot.RationalCoefficient
public import Colib.AlgebraicGeometry.ProjectiveLine.ChartInversionMap

/-!
# The constant root-field presentation and the native projective chart change

The actual constant-polynomial AdjoinRoot comparison intertwines the original
coefficient map induced by projectiveLineChartInversion and the actual chart
inversion on the rational function field of the original root field.

This is a square of the existing fields and maps, in arbitrary characteristic.
No chart change, quotient model, norm, or residue map is introduced.
-/

@[expose] public noncomputable section

open Polynomial
open scoped RatFunc
attribute [local instance] Polynomial.algebra

namespace AlgebraicGeometry

variable {k : Type*} [Field k]

/-- The literal constant polynomial is fixed by the native projective chart change. -/
theorem map_ratFunc_C_chartInversion (p : k[X]) :
    (p.map (RatFunc.C : k →+* RatFunc k)).map
      (projectiveLineChartInversion k).toRingHom = p.map RatFunc.C := by
  rw [Polynomial.map_map]
  congr 1
  ext c
  exact projectiveLineChartInversion_C k c

variable (p : k[X]) [Fact (Irreducible p)]

/-- The original root-field comparison intertwines the actual coefficient
quotient map and the existing inversion of the rational coordinate. -/
theorem rationalCoefficientAlgEquiv_map_chartInversion (hp : p.Monic)
    (x : AdjoinRoot (p.map (RatFunc.C : k →+* RatFunc k))) :
    AdjoinRoot.rationalCoefficientAlgEquiv p hp
      (AdjoinRoot.map (projectiveLineChartInversion k).toRingHom
        (p.map RatFunc.C) (p.map RatFunc.C)
        (by rw [map_ratFunc_C_chartInversion]; exact dvd_rfl) x) =
      projectiveLineChartInversion (AdjoinRoot p)
        (AdjoinRoot.rationalCoefficientAlgEquiv p hp x) := by
  have h : (AdjoinRoot.rationalCoefficientAlgEquiv p hp).toRingHom.comp
      (AdjoinRoot.map (projectiveLineChartInversion k).toRingHom
        (p.map RatFunc.C) (p.map RatFunc.C)
        (by rw [map_ratFunc_C_chartInversion]; exact dvd_rfl)) =
      (projectiveLineChartInversion (AdjoinRoot p)).toRingHom.comp
        (AdjoinRoot.rationalCoefficientAlgEquiv p hp).toRingHom := by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro r
      change AdjoinRoot.rationalCoefficientAlgEquiv p hp
        (AdjoinRoot.map _ _ _ _ (AdjoinRoot.of _ r)) =
        projectiveLineChartInversion (AdjoinRoot p)
          (AdjoinRoot.rationalCoefficientAlgEquiv p hp (AdjoinRoot.of _ r))
      rw [AdjoinRoot.map_of]
      change AdjoinRoot.rationalCoefficientAlgEquiv p hp
        (algebraMap (RatFunc k) _ (projectiveLineChartInversion k r)) =
        projectiveLineChartInversion (AdjoinRoot p)
          (AdjoinRoot.rationalCoefficientAlgEquiv p hp (algebraMap (RatFunc k) _ r))
      rw [AlgEquiv.commutes, AlgEquiv.commutes, RatFunc.algebraMap_eq_mapRingHom]
      exact (projectiveLineChartInversion_mapRingHom (algebraMap k (AdjoinRoot p)) r).symm
    · change AdjoinRoot.rationalCoefficientAlgEquiv p hp
        (AdjoinRoot.map _ _ _ _ (AdjoinRoot.root _)) =
        projectiveLineChartInversion (AdjoinRoot p)
          (AdjoinRoot.rationalCoefficientAlgEquiv p hp (AdjoinRoot.root _))
      rw [AdjoinRoot.map_root, AdjoinRoot.rationalCoefficientAlgEquiv_root]
      exact (projectiveLineChartInversion_C (AdjoinRoot p) (AdjoinRoot.root p)).symm
  exact RingHom.congr_fun h x

/-- The inverse comparison carries actual rational chart inversion to the
original coefficient map on the mapped polynomial quotient. -/
theorem rationalCoefficientAlgEquiv_symm_chartInversion (hp : p.Monic)
    (x : RatFunc (AdjoinRoot p)) :
    (AdjoinRoot.rationalCoefficientAlgEquiv p hp).symm
      (projectiveLineChartInversion (AdjoinRoot p) x) =
      AdjoinRoot.map (projectiveLineChartInversion k).toRingHom
        (p.map RatFunc.C) (p.map RatFunc.C)
        (by rw [map_ratFunc_C_chartInversion]; exact dvd_rfl)
        ((AdjoinRoot.rationalCoefficientAlgEquiv p hp).symm x) := by
  apply (AdjoinRoot.rationalCoefficientAlgEquiv p hp).injective
  rw [AlgEquiv.apply_symm_apply, rationalCoefficientAlgEquiv_map_chartInversion,
    AlgEquiv.apply_symm_apply]

end AlgebraicGeometry
