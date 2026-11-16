module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.BaseCoverGlue
public import Colib.AlgebraicGeometry.KTheory.SupportedMayerVietoris

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

example {V X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace V] [QuasiSeparatedSpace V] (j : V ⟶ X) [IsOpenImmersion j]
    (T : X.Opens) [CompactSpace T.toScheme] [CompactSpace (j ⁻¹ᵁ T).toScheme]
    (hc : ∀ x : X, x ∈ Set.range j ∨ x ∈ T) (n : ℕ) :
    Function.Bijective (X.projectiveLineKMap n) :=
  Scheme.projectiveLineKMap_bijective_of_baseOpenCover j T hc n

#print axioms Scheme.projectiveLineKMap_bijective_of_baseOpenCover
#print axioms Scheme.projectiveLineBaseCover_connecting
