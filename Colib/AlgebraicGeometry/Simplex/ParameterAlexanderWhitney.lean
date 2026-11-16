/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Simplex.ParameterTensorChains
/-! # Alexander–Whitney and native presheaf parameter reindexing -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory MonoidalCategory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
  AlgebraicTopology
open scoped Simplicial
universe u
namespace AlgebraicSimplex
variable (k : Type u) [Field k]
local notation "Sm" => SmoothSite (Spec (CommRingCat.of k))

/-- The native tensor comparison includes the actual alternating-chain/reindex
identifications on both factors. -/
def parameterAWTensorComparison (T : Sm)
    (M N : SimplicialObject (Smᵒᵖ ⥤ ModuleCat.{u + 1} ℤ)) :
    HomologicalComplex.tensorObj
      ((alternatingFaceMapComplex _).obj (M ⋙ parameterReindex k T))
      ((alternatingFaceMapComplex _).obj (N ⋙ parameterReindex k T)) ⟶
    ((parameterReindex k T).mapHomologicalComplex (.down ℕ)).obj
      (HomologicalComplex.tensorObj ((alternatingFaceMapComplex _).obj M)
        ((alternatingFaceMapComplex _).obj N)) :=
  HomologicalComplex.tensorHom
    ((alternatingFaceMapComplexCompMapHomologicalComplexIso (parameterReindex k T)).app M).inv
    ((alternatingFaceMapComplexCompMapHomologicalComplexIso (parameterReindex k T)).app N).inv ≫
    (parameterReindexChainsTensorIso k T
      ((alternatingFaceMapComplex (Smᵒᵖ ⥤ ModuleCat.{u + 1} ℤ)).obj M)
      ((alternatingFaceMapComplex (Smᵒᵖ ⥤ ModuleCat.{u + 1} ℤ)).obj N)).hom

end AlgebraicSimplex
