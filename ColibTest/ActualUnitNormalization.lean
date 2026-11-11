/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Sites.Smooth.Units.UnitNormalization

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicSimplex Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite

universe u

noncomputable section

variable (k : Type u) [Field k]

-- The fixed contraction is normalized without an extra hypothesis on the caller.
example :
    (unitSingularSheafHomotopyEquiv k).hom.f 0 ≫
      (HomologicalComplex.singleObjXSelf (.down ℕ) 0
        (largeUnitsSheaf (Spec (.of k)))).hom = inv (unitsSimplexPullback k 0) :=
  unitSingularSheafHomotopyEquiv_hom_f_zero_projection k

example :
    unitsSimplexPullback k 0 ≫ (unitSingularSheafHomotopyEquiv k).hom.f 0 ≫
      (HomologicalComplex.singleObjXSelf (.down ℕ) 0
        (largeUnitsSheaf (Spec (.of k)))).hom = 𝟙 _ :=
  unitsSimplexPullback_zero_projection k

-- This evaluates the same composite on every smooth object, including nonaffine ones.
example (X : SmoothSite (Spec (.of k)))
    (v : (largeUnitsPresheaf (Spec (.of k))).obj (op X)) :
    ((unitsSimplexPullback k 0 ≫ (unitSingularSheafHomotopyEquiv k).hom.f 0 ≫
      (HomologicalComplex.singleObjXSelf (.down ℕ) 0
        (largeUnitsSheaf (Spec (.of k)))).hom).hom.app (op X)) v = v := by
  rw [unitsSimplexPullback_zero_projection]
  rfl

example (n : ℕ) :
    (unitSheafifiedSingularIso k).hom.f n =
      (sheafificationAdjunction (nisnevichTopology (Spec (.of k)))
        AddCommGrpCat.{u + 1}).counit.app ((unitSingularSheafComplex k).X n) :=
  unitSheafifiedSingularIso_hom_f k n

example (n : ℕ) :
    toSheafify (nisnevichTopology (Spec (.of k)))
        (((singularChainsFunctor k).obj (largeUnitsPresheaf (Spec (.of k)))).X n) ≫
      ((unitSheafifiedSingularIso k).hom.f n).hom = 𝟙 _ :=
  toSheafify_unitSheafifiedSingularIso_hom_f k n
