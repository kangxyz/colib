/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Simplex.SimplicialParameterInsertionFactor
public import Colib.AlgebraicTopology.ConstantCoordinateSingle
/-! # The original projection and coordinate in reindexed native chains -/
@[expose] public noncomputable section
open CategoryTheory MonoidalCategory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
  AlgebraicTopology
universe u
namespace AlgebraicSimplex
variable (k : Type u) [Field k]
local notation "Sm" => SmoothSite (Spec (CommRingCat.of k))

/-- Actual projection pullback followed by the native alternating/reindex inverse. -/
def parameterChainProjection (P : Smᵒᵖ ⥤ ModuleCat.{u + 1} ℤ) (T : Sm) :
    (singularChainsFunctor k).obj P ⟶
      ((parameterReindex k T).mapHomologicalComplex (.down ℕ)).obj
        ((singularChainsFunctor k).obj P) :=
  (alternatingFaceMapComplex _).map (simplicialParameterProjectionPullback k P T) ≫
    ((alternatingFaceMapComplexCompMapHomologicalComplexIso
      (parameterReindex k T)).app (simplicialPresheaf k P)).inv

/-- The original constant coordinate, precomposed with native inverse augmentation
and transported by the native alternating/reindex inverse. -/
def parameterChainCoordinate (Q : Smᵒᵖ ⥤ ModuleCat.{u + 1} ℤ)
    (T : Sm) (b : Q.obj (op T)) :
    HomologicalComplex.tensorUnit (Smᵒᵖ ⥤ ModuleCat.{u + 1} ℤ) (.down ℕ) ⟶
      ((parameterReindex k T).mapHomologicalComplex (.down ℕ)).obj
        ((singularChainsFunctor k).obj Q) :=
  constantCoordinateSingle (simplicialPresheaf k Q ⋙ parameterReindex k T)
    (𝟙_ (Smᵒᵖ ⥤ ModuleCat.{u + 1} ℤ)) (simplicialConstantParameterCoordinate k Q T b) ≫
    ((alternatingFaceMapComplexCompMapHomologicalComplexIso
      (parameterReindex k T)).app (simplicialPresheaf k Q)).inv

end AlgebraicSimplex
