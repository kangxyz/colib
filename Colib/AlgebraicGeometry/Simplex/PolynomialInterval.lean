/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Simplex.Prism
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.AffineComparison
import Mathlib.Tactic.FinCases

/-!
# The polynomial affine line and the barycentric interval

The established simplex chart keeps barycentric coordinate zero as the
polynomial variable. Consequently its two vertex maps evaluate the
polynomial variable at one and zero, respectively. The comparison also
identifies the actual sections of the native affine-line cylinder.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite.Contraction
open scoped Simplicial

universe u

namespace AlgebraicSimplex

variable (R : Type u) [CommRing R]

/-- The established algebraic interval chart with its single polynomial variable. -/
def intervalPolynomialEquiv : CoordinateRing R 1 ≃ₐ[R] Polynomial R :=
  (polynomialEquiv R 1).trans (MvPolynomial.uniqueAlgEquiv R (Fin 1))

/-- The polynomial affine line is the original algebraic interval in its
existing last-coordinate-elimination chart. -/
def polynomialLineSimplexIso :
    polynomialAffineLine (.of R) ≅ (cosimplicialSmoothSite R).obj ⦋1⦌ := by
  let e := intervalPolynomialEquiv R
  let i : (polynomialAffineLine (.of R)).left ≅
      ((cosimplicialSmoothSite R).obj ⦋1⦌).left :=
    Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op
  refine MorphismProperty.Over.isoMk i ?_
  change Spec.map (CommRingCat.ofHom e.toRingHom) ≫ structureMap R 1 =
    Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))
  rw [structureMap, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext e.commutes

private theorem intervalPolynomialEquiv_coordinate_zero :
    intervalPolynomialEquiv R (coordinate R 1 0) = Polynomial.X := by
  change MvPolynomial.uniqueAlgEquiv R (Fin 1)
    (polynomialEquiv R 1 (coordinate R 1 (Fin.castSucc (0 : Fin 1)))) = _
  rw [polynomialEquiv_coordinate_castSucc]
  exact MvPolynomial.eval₂_X _ _ _

private theorem intervalPolynomialEquiv_coordinate_one :
    intervalPolynomialEquiv R (coordinate R 1 1) = 1 - Polynomial.X := by
  change MvPolynomial.uniqueAlgEquiv R (Fin 1)
    (polynomialEquiv R 1 (coordinate R 1 (Fin.last 1))) = _
  rw [polynomialEquiv_coordinate_last, map_sub, map_one, map_sum, Fin.sum_univ_one]
  exact congrArg (fun p : Polynomial R => 1 - p) (MvPolynomial.eval₂_X _ _ _)

private theorem intervalPolynomialEquiv_eval_vertex (v : Fin 2) :
    (Polynomial.evalRingHom (if v = 0 then (1 : R) else 0)).comp
      (intervalPolynomialEquiv R).toRingHom = vertexEvaluation R v := by
  apply ringHom_ext
  · intro r
    change Polynomial.eval (if v = 0 then (1 : R) else 0)
        (intervalPolynomialEquiv R (constant R 1 r)) = _
    rw [show intervalPolynomialEquiv R (constant R 1 r) = Polynomial.C r from
      (intervalPolynomialEquiv R).commutes r, Polynomial.eval_C, vertexEvaluation_constant]
  · intro i
    fin_cases i <;> fin_cases v <;>
      simp [intervalPolynomialEquiv_coordinate_zero, intervalPolynomialEquiv_coordinate_one]

/-- Vertex zero evaluates the polynomial variable at one and vertex one
evaluates it at zero. -/
theorem polynomialAffinePoint_comp_polynomialLineSimplexIso (v : Fin 2) :
    polynomialAffinePoint (.of R) (if v = 0 then 1 else 0) ≫ (polynomialLineSimplexIso R).hom =
      vertexAt R (SmoothSite.base (Spec (.of R))) v := by
  apply MorphismProperty.Over.Hom.ext
  change Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (if v = 0 then 1 else 0))) ≫
      Spec.map (CommRingCat.ofHom (intervalPolynomialEquiv R).toRingHom) =
    𝟙 _ ≫ Spec.map (CommRingCat.ofHom (vertexEvaluation R v))
  rw [← Spec.map_comp, Category.id_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (DFunLike.congr_fun (intervalPolynomialEquiv_eval_vertex R v))

/-- The native affine-line cylinder compared to the original barycentric interval. -/
def nativeAffineCylinderIntervalIso (U : SmoothSite (Spec (.of R))) :
    affineLineCylinder.obj U ≅ SmoothSite.product U ((cosimplicialSmoothSite R).obj ⦋1⦌) :=
  affineCylinderPolynomialIso (.of R) U ≪≫
    { hom := SmoothSite.productMap (𝟙 U) (polynomialLineSimplexIso R).hom
      inv := SmoothSite.productMap (𝟙 U) (polynomialLineSimplexIso R).inv
      hom_inv_id := by
        rw [← SmoothSite.productMap_comp]
        simp only [Category.id_comp, Iso.hom_inv_id, SmoothSite.productMap_id]
      inv_hom_id := by
        rw [← SmoothSite.productMap_comp]
        simp only [Category.id_comp, Iso.inv_hom_id, SmoothSite.productMap_id] }

/-- The native cylinder comparison carries literal scalar sections to
the corresponding vertex sections, with the chart's endpoint order. -/
@[reassoc]
theorem nativeAffineSection_comp_intervalIso (U : SmoothSite (Spec (.of R))) (v : Fin 2) :
    nativeAffineSection (.of R) U (if v = 0 then 1 else 0) ≫
      (nativeAffineCylinderIntervalIso R U).hom = intervalInclusion R U v := by
  rw [nativeAffineCylinderIntervalIso, Iso.trans_hom, ← Category.assoc,
    nativeAffineSection_polynomialIso]
  apply SmoothSite.product_hom_ext
  · simp [polynomialAffineSection, intervalInclusion]
  · simp only [Category.assoc, SmoothSite.productMap_snd, polynomialAffineSection,
      intervalInclusion, SmoothSite.productLift_snd_assoc, SmoothSite.productLift_snd]
    rw [polynomialAffinePoint_comp_polynomialLineSimplexIso, comp_vertexAt]

end AlgebraicSimplex
