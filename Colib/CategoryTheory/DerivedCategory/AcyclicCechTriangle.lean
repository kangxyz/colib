/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyComparison.Natural

/-!
# The derived triangle of a two-term acyclic resolution

The acyclic terms of a short exact sequence can be placed in degree zero
after applying a right derived functor. The second arrow is then literally
the original differential; the third arrow is the canonical derived
connecting morphism composed with the acyclic comparison unit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated
open Stacks.Cohomology.AffineComparison Stacks.DerivedIndexing

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace CategoryTheory.Functor

variable {A B : Type*} [Category* A] [Category* B]
  [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
  [EnoughInjectives A] (F : A ⥤ B) [F.Additive]
  [F.rightDerivedFunctorPlus.CommShift ℤ] [F.rightDerivedFunctorPlus.IsTriangulated]
  {S : ShortComplex A} (hS : S.ShortExact)

/-- The canonical derived image of the single triangle of a short exact sequence. -/
def rightDerivedSingleTriangle : Triangle (DerivedCategory.Plus B) :=
  F.rightDerivedFunctorPlus.mapTriangle.obj
    (Triangle.mk ((DerivedCategory.Plus.singleFunctor A 0).map S.f)
      ((DerivedCategory.Plus.singleFunctor A 0).map S.g) (singleδPlus hS))

variable (h₂ : F.rightAcyclic S.X₂) (h₃ : F.rightAcyclic S.X₃)

/-- The triangle with the literal differential after identifying its acyclic vertices. -/
def rightDerivedAcyclicTriangle : Triangle (DerivedCategory.Plus B) :=
  Triangle.mk
    ((rightDerivedSingleTriangle F hS).mor₁ ≫
      (rightDerivedFunctorPlusObjSingleIso F S.X₂ h₂).hom)
    ((DerivedCategory.Plus.singleFunctor B 0).map (F.map S.g))
    ((rightDerivedFunctorPlusObjSingleIso F S.X₃ h₃).inv ≫
      (rightDerivedSingleTriangle F hS).mor₃)

/-- Comparison with the original derived triangle, including its connecting arrow. -/
def rightDerivedAcyclicTriangleIso :
    rightDerivedAcyclicTriangle F hS h₂ h₃ ≅ rightDerivedSingleTriangle F hS := by
  let e₂ := rightDerivedFunctorPlusObjSingleIso F S.X₂ h₂
  let e₃ := rightDerivedFunctorPlusObjSingleIso F S.X₃ h₃
  refine Triangle.isoMk _ _ (Iso.refl _) e₂.symm e₃.symm ?_ ?_ ?_
  · change (F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor A 0).map S.f) ≫
        e₂.hom) ≫ e₂.inv = 𝟙 _ ≫
      F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor A 0).map S.f)
    rw [Category.assoc, e₂.hom_inv_id, Category.comp_id, Category.id_comp]
  · change (DerivedCategory.Plus.singleFunctor B 0).map (F.map S.g) ≫ e₃.inv =
      e₂.inv ≫ F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor A 0).map S.g)
    have h := (singleRightDerivedUnit F).naturality S.g
    rw [singleRightDerivedUnit_app F _ h₂, singleRightDerivedUnit_app F _ h₃] at h
    exact h
  · change (e₃.inv ≫ _) ≫ (𝟙 _)⟦(1 : ℤ)⟧' = e₃.inv ≫ _
    rw [Functor.map_id, Category.comp_id]

/-- This is a distinguished triangle, with its original derived boundary. -/
theorem rightDerivedAcyclicTriangle_distinguished :
    rightDerivedAcyclicTriangle F hS h₂ h₃ ∈ distTriang (DerivedCategory.Plus B) :=
  isomorphic_distinguished _ (F.rightDerivedFunctorPlus.map_distinguished _
    (singleTrianglePlus_distinguished hS)) _ (rightDerivedAcyclicTriangleIso F hS h₂ h₃)

end CategoryTheory.Functor
