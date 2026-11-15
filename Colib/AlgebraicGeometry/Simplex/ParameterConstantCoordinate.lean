/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Simplex.TensorParameterInsertion
/-! # The fixed parameter coordinate as a genuinely constant simplicial source -/
@[expose] public noncomputable section
open CategoryTheory MonoidalCategory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
universe u
namespace AlgebraicSimplex
variable (k : Type u) [Field k]
local notation "Sm" => SmoothSite (Spec (CommRingCat.of k))

/-- Singular simplices of the actual pointwise tensor unit are constant. -/
def simplicialPresheafTensorUnitIso :
    (SimplicialObject.const (Smᵒᵖ ⥤ ModuleCat.{u + 1} ℤ)).obj (𝟙_ (Smᵒᵖ ⥤ ModuleCat.{u + 1} ℤ)) ≅
      simplicialPresheaf k (𝟙_ (Smᵒᵖ ⥤ ModuleCat.{u + 1} ℤ)) :=
  Iso.refl _

/-- The fixed section defines a native map from the tensor unit into parameter sections. -/
def parameterUnitCoordinate (Q : (Smᵒᵖ ⥤ ModuleCat.{u + 1} ℤ)) (T : Sm) (b : Q.obj (op T)) :
    𝟙_ (Smᵒᵖ ⥤ ModuleCat.{u + 1} ℤ) ⟶ (parameterReindex k T).obj Q :=
  tensorParameterInsertion k (𝟙_ (Smᵒᵖ ⥤ ModuleCat.{u + 1} ℤ)) Q T b ≫
    (parameterReindex k T).map (λ_ Q).hom

/-- The coordinate is a map from a constant simplicial unit into the actual
parameter-reindexed singular presheaf, using the native simplex/parameter swap. -/
def simplicialConstantParameterCoordinate (Q : (Smᵒᵖ ⥤ ModuleCat.{u + 1} ℤ))
    (T : Sm) (b : Q.obj (op T)) :
    (SimplicialObject.const (Smᵒᵖ ⥤ ModuleCat.{u + 1} ℤ)).obj (𝟙_ (Smᵒᵖ ⥤ ModuleCat.{u + 1} ℤ)) ⟶
      ((SimplicialObject.whiskering (Smᵒᵖ ⥤ ModuleCat.{u + 1} ℤ)
        (Smᵒᵖ ⥤ ModuleCat.{u + 1} ℤ)).obj (parameterReindex k T)).obj
        (simplicialPresheaf k Q) :=
  (simplicialPresheafTensorUnitIso k).hom ≫
    (simplicialPresheafFunctor k).map (parameterUnitCoordinate k Q T b) ≫
      (simplicialPresheafParameterIso k T Q).hom

end AlgebraicSimplex
