/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Additive.Ext
public import Colib.AlgebraicGeometry.Correspondences.Category
public import Colib.AlgebraicGeometry.Correspondences.Exterior.Simplex.Geometry

/-!
# Additive exterior action of the actual algebraic simplex

Each native prime cycle is sent to the prime on its literal product support,
embedded using one shared simplex coordinate. The signed additive extension
uses `liftFiniteCorrespondence` on the native algebraic-cycle subgroup.
Composition and mixed graph interchange are separate obligations.

Implementation source:
`Motivic/AlgebraicGeometry/Correspondences/Exterior/Simplex/Basic.lean`
and `Exterior/Identity/Basic.lean`, commit `a6805c4a87cdfd7717dd7a94039246a167f15380`.
The source's `Finsupp` extension is replaced by the native prime-cycle extension.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k] {X Y : SmoothSite (Spec (.of k))}

/-- Exterior multiplication by the identity simplex on the native signed correspondence group. -/
def simplexExterior (n : ℕ) : finiteCorrespondences X.hom Y.hom →+
    finiteCorrespondences (SmoothSite.product X (AlgebraicSimplex.smoothSiteObj k n)).hom
      (SmoothSite.product Y (AlgebraicSimplex.smoothSiteObj k n)).hom :=
  liftFiniteCorrespondence X.hom Y.hom fun z hz =>
    singleFiniteCorrespondence _ _ (simplexExteriorPoint z n hz)
      (simplexExteriorPoint_admissible z n hz) 1

/-- Every integer coefficient is retained on the actual exterior prime. -/
theorem simplexExterior_single (n : ℕ) (z : pullback (C := Scheme) X.hom Y.hom)
    (hz : IsFiniteCorrespondencePoint X.hom Y.hom z) (m : ℤ) :
    @Eq (finiteCorrespondences
      (SmoothSite.product X (AlgebraicSimplex.smoothSiteObj k n)).hom
      (SmoothSite.product Y (AlgebraicSimplex.smoothSiteObj k n)).hom)
      (simplexExterior (X := X) (Y := Y) n
        (singleFiniteCorrespondence X.hom Y.hom z hz m))
      (singleFiniteCorrespondence
        (SmoothSite.product X (AlgebraicSimplex.smoothSiteObj k n)).hom
        (SmoothSite.product Y (AlgebraicSimplex.smoothSiteObj k n)).hom
        (simplexExteriorPoint z n hz) (simplexExteriorPoint_admissible z n hz) m) := by
  rw [simplexExterior, liftFiniteCorrespondence_single]
  exact (singleFiniteCorrespondence_eq_zsmul
    (SmoothSite.product X (AlgebraicSimplex.smoothSiteObj k n)).hom
    (SmoothSite.product Y (AlgebraicSimplex.smoothSiteObj k n)).hom
    (simplexExteriorPoint z n hz) (simplexExteriorPoint_admissible z n hz) m).symm

end Stacks.Chow

namespace AlgebraicGeometry.Cor

variable {k : Type u} [Field k]

/-- The actual smooth product with the simplex, regarded as a correspondence object. -/
def simplexProduct (X : Cor k) (n : ℕ) : Cor k :=
  ⟨SmoothSite.product X.toSmoothSite (AlgebraicSimplex.smoothSiteObj k n)⟩

/-- The additive exterior operation on the existing hom groups of `Cor k`. -/
def simplexExterior {X Y : Cor k} (n : ℕ) :
    (X ⟶ Y) →+ (simplexProduct X n ⟶ simplexProduct Y n) :=
  Stacks.Chow.simplexExterior n

@[simp]
theorem simplexExterior_add {X Y : Cor k} (n : ℕ) (α β : X ⟶ Y) :
    simplexExterior n (α + β) = simplexExterior n α + simplexExterior n β :=
  map_add _ _ _

@[simp]
theorem simplexExterior_neg {X Y : Cor k} (n : ℕ) (α : X ⟶ Y) :
    simplexExterior n (-α) = -simplexExterior n α := map_neg _ _

@[simp]
theorem simplexExterior_zsmul {X Y : Cor k} (n : ℕ) (m : ℤ) (α : X ⟶ Y) :
    simplexExterior n (m • α) = m • simplexExterior n α := map_zsmul _ _ _

end AlgebraicGeometry.Cor
