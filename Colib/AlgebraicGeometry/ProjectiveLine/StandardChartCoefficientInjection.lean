/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.StandardChartBaseProjection
public import Colib.AlgebraicGeometry.KTheory.PerfectPullbackCompatibility
public import Colib.AlgebraicGeometry.Scheme.QuasiCompactPolynomialZeroSection

/-! # The coefficient injection on an original standard chart -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveLine

/-- Zero evaluation on the native polynomial chart splits the map of coefficient groups. -/
theorem relativePolynomialPullback_injective (X : QuasiCompactSchemes.{u}) (n : ℕ) :
    Function.Injective (perfectKPullback (Relative.polynomialProjection.app X).hom n) := by
  let p := (Relative.polynomialProjection.app X).hom
  let z := (AlgebraicGeometry.Scheme.Bass.polynomialZero.app X).hom
  have h : z ≫ p = 𝟙 X.obj :=
    congrArg (fun f => f.hom) (AlgebraicGeometry.Scheme.Bass.polynomialZero_projection X)
  have hh := (perfectKPullback_comp z p n).symm.trans
    ((congrArg (fun f => perfectKPullback f n) h).trans (perfectKPullback_id X.obj n))
  intro a b e
  exact ((DFunLike.congr_fun hh a).symm.trans
    ((congrArg (perfectKPullback z n) e).trans (DFunLike.congr_fun hh b)))

/-- The map of coefficient groups on the original standard chart is injective. -/
theorem standardChartCoefficientPullback_injective (X : QuasiCompactSchemes.{u})
    (i : Fin 2) (n : ℕ) :
    Function.Injective (perfectKPullback ((standardChart X.obj i).ι ≫
      (projectiveSpaceOver 1 X.obj ↘ X.obj)) n) := by
  let e := standardChartPolynomialIso X i
  let : CompactSpace (standardChart X.obj i).toScheme :=
    (Scheme.homeoOfIso e).symm.compactSpace
  rw [← standardChartPolynomialIso_projection X i, perfectKPullback_comp]
  change Function.Injective ((perfectKPullback e.hom n) ∘
    (perfectKPullback (Relative.polynomialProjection.app X).hom n))
  refine Function.Injective.comp ?_ (relativePolynomialPullback_injective X n)
  intro a b h
  have hh := (perfectKPullback_comp e.inv e.hom n).symm.trans
    ((congrArg (fun f => perfectKPullback f n) e.inv_hom_id).trans (perfectKPullback_id _ n))
  exact (DFunLike.congr_fun hh a).symm.trans
    ((congrArg (perfectKPullback e.inv n) h).trans (DFunLike.congr_fun hh b))

end AlgebraicGeometry.Scheme.ProjectiveLine
