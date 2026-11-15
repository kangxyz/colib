/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Simplex.ParameterProduct
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusPresheafAW
public import StacksFrontier.Homology.MapHomologicalComplexMonoidal

/-! # The native total-tensor comparison for presheaf parameter reindexing

This is a comparison of presheaf chains, not a claim about exactness of
parameter sections of sheaves.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
universe u
namespace AlgebraicSimplex
variable (k : Type u) [Field k]

/-- Presheaf parameter reindexing commutes with the actual chain total tensor. -/
def parameterReindexChainsTensorIso
    (T : SmoothSite (Spec (CommRingCat.of k)))
    (K L : ChainComplex ((SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ ⥤
      ModuleCat.{u + 1} ℤ) ℕ) :
    HomologicalComplex.tensorObj
      (((parameterReindex k (A := ModuleCat.{u + 1} ℤ) T).mapHomologicalComplex
        (.down ℕ)).obj K)
      (((parameterReindex k (A := ModuleCat.{u + 1} ℤ) T).mapHomologicalComplex
        (.down ℕ)).obj L) ≅
    ((parameterReindex k (A := ModuleCat.{u + 1} ℤ) T).mapHomologicalComplex
      (.down ℕ)).obj (HomologicalComplex.tensorObj K L) :=
  Functor.mapHomologicalComplexTensorator
    (parameterReindex k (A := ModuleCat.{u + 1} ℤ) T) K L

end AlgebraicSimplex
