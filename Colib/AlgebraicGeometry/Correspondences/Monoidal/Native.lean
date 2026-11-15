/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Monoidal.AssociatorNaturality
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.ConstraintNaturality
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.RightParameter
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.UnitNaturality

/-!
# The native symmetric additive tensor on finite correspondences

Tensor on objects is the literal product of the original smooth schemes.
Tensor on arrows is the exterior product of their signed finite cycles.
The unit, associator and symmetry have the graphs of the actual scheme
isomorphisms as their constraints.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory BraidedCategory
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

/-- The canonical factor switch is the braiding of the smooth site. -/
instance braidedCategory (S : Scheme.{u}) : BraidedCategory (SmoothSite S) :=
  BraidedCategory.ofCartesianMonoidalCategory

end AlgebraicGeometry.Scheme.SmoothSite

namespace AlgebraicGeometry.Cor

variable {k : Type u} [Field k]

variable [PerfectField k]

/-- The native signed finite correspondences form a monoidal category over a perfect field. -/
instance monoidalCategory : MonoidalCategory (Cor k) :=
  exteriorMonoidalCategory exteriorInterchange exteriorGraphProduct exteriorAssociatorNaturality
    exteriorRightUnitorNaturality exteriorBraidingNaturality

/-- Switching the two source and target factors is the symmetry of finite correspondences. -/
instance symmetricCategory : SymmetricCategory (Cor k) :=
  exteriorSymmetricCategory exteriorInterchange exteriorGraphProduct exteriorAssociatorNaturality
    exteriorRightUnitorNaturality exteriorBraidingNaturality

/-- Each whiskering is additive on signed finite correspondences. -/
instance monoidalPreadditive : MonoidalPreadditive (Cor k) :=
  exteriorMonoidalPreadditive exteriorInterchange exteriorGraphProduct exteriorAssociatorNaturality
    exteriorRightUnitorNaturality exteriorBraidingNaturality

/-- The ordinary graph functor is strong braided for the literal product. -/
instance graphFunctorBraided : (graphFunctor k).Braided :=
  exteriorGraphBraided exteriorInterchange exteriorGraphProduct exteriorAssociatorNaturality
    exteriorRightUnitorNaturality exteriorBraidingNaturality

/-- The monoidal tensor on arrows is the native signed exterior product. -/
theorem tensorHom_eq_exteriorProduct {X Y U V : Cor k} (a : X ⟶ Y) (b : U ⟶ V) :
    a ⊗ₘ b = exteriorProduct a b := rfl

/-- On ordinary maps the tensor is the graph of the actual scheme product map. -/
@[simp]
theorem tensorHom_graph {X Y U V : SmoothSite (Spec (.of k))} (f : X ⟶ Y) (g : U ⟶ V) :
    (graphFunctor k).map f ⊗ₘ (graphFunctor k).map g =
      (graphFunctor k).map (SmoothSite.productMap f g) :=
  exteriorProduct_graph f g

/-- Tensor with the identity of a geometrically integral parameter is the original fixed
parameter map on finite correspondences. -/
theorem whiskerRight_eq_nativeExterior (T : SmoothSite (Spec (.of k)))
    [GeometricallyIntegral T.hom] {X Y : Cor k} (a : X ⟶ Y) :
    a ▷ Cor.mk T = Stacks.Chow.nativeExterior X.toSmoothSite Y.toSmoothSite T a :=
  exteriorProduct_identity_right T a

/-- The canonical tensor bifunctor preserves the explicit signed cycles in each input. -/
theorem tensor_map_eq_exteriorProduct {X Y U V : Cor k}
    (a : X ⟶ Y) (b : U ⟶ V) :
    (MonoidalCategory.tensor (Cor k)).map ((a, b) : (X, U) ⟶ (Y, V)) =
      exteriorProduct a b := rfl

/-- Right tensoring an ordinary graph is the graph of the literal parameter product. -/
def graphFunctorCompTensorRightIso (T : SmoothSite (Spec (.of k))) :
    graphFunctor k ⋙ tensorRight (Cor.mk T) ≅
      SmoothSite.Contraction.parameterProduct T ⋙ graphFunctor k :=
  graphFunctorCompRightExteriorParameterIso T

end AlgebraicGeometry.Cor
