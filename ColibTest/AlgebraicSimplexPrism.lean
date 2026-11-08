/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Simplex.EndpointHomotopy
import Mathlib.Data.ZMod.Basic

/-! # Consumers of the native ordinal prism and original singular endpoint maps -/

noncomputable section

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite AlgebraicTopology
open AlgebraicGeometry.Scheme AlgebraicSimplex
open scoped Simplicial

universe u v w

variable (R : Type u) [CommRing R]

example (n : ℕ) :
    SimplexCategory.δ (0 : Fin (n + 2)) ≫
      SimplexCategory.toMk₁ (0 : Fin (n + 1)).castSucc.succ =
        SimplexCategory.const ⦋n⦌ ⦋1⦌ 1 :=
  SimplexCategory.δ_zero_comp_toMk₁_prism n

example : vertexEvaluation (ZMod 6) 0 (coordinate (ZMod 6) 1 0) = 1 := by simp

example : vertexEvaluation (ZMod 6) 0 (coordinate (ZMod 6) 1 1) = 0 := by simp

example : vertexEvaluation (ZMod 6) 1 (coordinate (ZMod 6) 1 0) = 0 := by simp

example : vertexEvaluation (ZMod 6) 1 (coordinate (ZMod 6) 1 1) = 1 := by simp

example (U : SmoothSite (Spec (.of R))) (v : Fin 2) :
    intervalInclusion R U v ≫ SmoothSite.productFst U (smoothSiteObj R 1) = 𝟙 U :=
  intervalInclusion_fst R U v

example (n : ℕ) (v : Fin 2) :
    (cosimplicialSmoothSite R).map (SimplexCategory.const ⦋n⦌ ⦋1⦌ v) =
      vertexAt R (smoothSiteObj R n) v := map_const_eq_vertexAt R n v

example (U : SmoothSite (Spec (.of R))) (n : ℕ) :
    SmoothSite.productMap (𝟙 U) ((cosimplicialSmoothSite R).δ (0 : Fin (n + 2))) ≫
      prismMap R U (0 : Fin (n + 1)) =
        SmoothSite.productMap (intervalInclusion R U 1) (𝟙 (smoothSiteObj R n)) :=
  prismMap_zero_face R U n

example (U : SmoothSite (Spec (.of R))) (n : ℕ) :
    SmoothSite.productMap (𝟙 U) ((cosimplicialSmoothSite R).δ (Fin.last (n + 1))) ≫
      prismMap R U (Fin.last n) =
        SmoothSite.productMap (intervalInclusion R U 0) (𝟙 (smoothSiteObj R n)) :=
  prismMap_last_face R U n

variable {A : Type v} [Category.{w} A] [Preadditive A]
variable (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A)

example (U : SmoothSite (Spec (.of R))) :
    Nonempty (SimplicialObject.Homotopy
      ((simplicialPresheaf R P).flip.map (intervalInclusion R U 0).op)
      ((simplicialPresheaf R P).flip.map (intervalInclusion R U 1).op)) :=
  ⟨intervalEndpointSimplicialHomotopy R P U⟩

example (U : SmoothSite (Spec (.of R))) (n : ℕ) :
    (intervalEndpointHomotopy R P U).hom n (n + 1) =
      -∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • P.map (prismMap R U i).op :=
  intervalEndpointHomotopy_hom R P U n

example (U : SmoothSite (Spec (.of R))) (v : Fin 2) (n : ℕ) :
    (((NatTrans.mapHomologicalComplex
      ((evaluation _ A).map (intervalInclusion R U v).op)
      (ComplexShape.down ℕ)).app ((singularChainsFunctor R).obj P)).f n) =
        P.map (SmoothSite.productMap (intervalInclusion R U v)
          (𝟙 (smoothSiteObj R n))).op := rfl

example (U : SmoothSite (Spec (.of R))) :
    Nonempty (_root_.Homotopy
      ((NatTrans.mapHomologicalComplex
        ((evaluation _ A).map (intervalInclusion R U 0).op)
        (ComplexShape.down ℕ)).app ((singularChainsFunctor R).obj P))
      ((NatTrans.mapHomologicalComplex
        ((evaluation _ A).map (intervalInclusion R U 1).op)
        (ComplexShape.down ℕ)).app ((singularChainsFunctor R).obj P))) :=
  ⟨ordinaryIntervalEndpointHomotopy R P U⟩

example [CategoryWithHomology A] (U : SmoothSite (Spec (.of R))) (n : ℕ) :
    HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex
        ((evaluation _ A).map (intervalInclusion R U 0).op)
        (ComplexShape.down ℕ)).app ((singularChainsFunctor R).obj P)) n =
      HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex
          ((evaluation _ A).map (intervalInclusion R U 1).op)
          (ComplexShape.down ℕ)).app ((singularChainsFunctor R).obj P)) n :=
  ordinaryIntervalEndpoint_homologyMap_eq R P U n
