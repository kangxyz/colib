/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Simplex.GeometricallyIntegral
public import Colib.AlgebraicGeometry.Correspondences.Exterior.Graph
public import Colib.AlgebraicGeometry.Correspondences.Exterior.GraphInterchange

/-!
# The actual simplex specialization of native exterior

Use the existing literal relative simplex product and specialize the already
constructed signed native exterior operation. The graph and identity equations,
and mixed graph interchange for all simplex operators, are specializations of
the existing general native theorems. No second support presentation is needed.

This gives the native implementation of the original
`Motivic/AlgebraicGeometry/Correspondences/Exterior/Simplex/Basic.lean`
at a6805c4a87cdfd7717dd7a94039246a167f15380. Composition is in the precise
separate functor owner and uses the actual general incidence Tor composition.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Cor

variable {k : Type u} [Field k]

/-- The original literal smooth product with the algebraic simplex. -/
def simplexProduct (X : Cor k) (n : ℕ) : Cor k :=
  Cor.mk (SmoothSite.product X.toSmoothSite (AlgebraicSimplex.smoothSiteObj k n))

/-- The existing signed native exterior map at the actual simplex parameter. -/
def simplexExterior {X Y : Cor k} (n : ℕ) :
    (X ⟶ Y) →+ (simplexProduct X n ⟶ simplexProduct Y n) :=
  Stacks.Chow.nativeExterior X.toSmoothSite Y.toSmoothSite
    (AlgebraicSimplex.smoothSiteObj k n)

@[simp]
theorem simplexExterior_add {X Y : Cor k} (n : ℕ) (α β : X ⟶ Y) :
    simplexExterior n (α + β) = simplexExterior n α + simplexExterior n β := map_add _ _ _

@[simp]
theorem simplexExterior_neg {X Y : Cor k} (n : ℕ) (α : X ⟶ Y) :
    simplexExterior n (-α) = -simplexExterior n α := map_neg _ _

@[simp]
theorem simplexExterior_zsmul {X Y : Cor k} (n : ℕ) (m : ℤ) (α : X ⟶ Y) :
    simplexExterior n (m • α) = m • simplexExterior n α := map_zsmul _ _ _

/-- Exterior multiplication by the simplex preserves each actual signed graph. -/
theorem simplexExterior_graph (n : ℕ) {X Y : SmoothSite (Spec (.of k))} (φ : X ⟶ Y) :
    simplexExterior n ((graphFunctor k).map φ) =
      (graphFunctor k).map
        (SmoothSite.productMap φ (𝟙 (AlgebraicSimplex.smoothSiteObj k n))) :=
  Stacks.Chow.nativeExterior_graphFunctor X Y (AlgebraicSimplex.smoothSiteObj k n) φ

/-- The actual correspondence identity is preserved, including disconnected sources. -/
@[simp]
theorem simplexExterior_id (n : ℕ) (X : Cor k) :
    simplexExterior n (𝟙 X) = 𝟙 (simplexProduct X n) := by
  cases X with
  | mk U => exact Stacks.Chow.nativeExterior_id U (AlgebraicSimplex.smoothSiteObj k n)

/-- Original mixed interchange for every simplex operator, without a flatness assumption. -/
theorem simplexExterior_graph_interchange {n m : ℕ}
    (ψ : AlgebraicSimplex.smoothSiteObj k n ⟶ AlgebraicSimplex.smoothSiteObj k m)
    {X Y : Cor k} (α : X ⟶ Y) :
    simplexExterior n α ≫
        (graphFunctor k).map (SmoothSite.productMap (𝟙 Y.toSmoothSite) ψ) =
      (graphFunctor k).map (SmoothSite.productMap (𝟙 X.toSmoothSite) ψ) ≫
        simplexExterior m α := by
  simpa only [simplexExterior] using!
    (Stacks.Chow.nativeExterior_graph_interchange X.toSmoothSite Y.toSmoothSite
      (AlgebraicSimplex.smoothSiteObj k n) (AlgebraicSimplex.smoothSiteObj k m) ψ α).symm

end AlgebraicGeometry.Cor
