/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Etale.DerivedRestriction

/-!
# Full-small derived restriction at the original smooth scheme

Specialize the actual separated finite-type neighborhood comparison to the
identity neighborhood. Its big image maps to the original smooth object by the
identity scheme map; its full-small image is identified by the existing canonical
isomorphism with the actual terminal etale object. The coefficient complex is
still the original restricted complex, not a Tate coefficient sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Stacks.Cohomology.FreeYonedaUnivLE

universe u w w'

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {B : Scheme.{u}} [IsAffine B] (X : SmoothSite B)
variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.etaleTopology B) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{w'} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- Actual full-small derived restriction at `X`, with its genuine terminal small source. -/
@[colib_tag "COL-1232"]
def fullSmallDerivedHomMapAtBase
    (K : CochainComplex (Sheaf (SmoothSite.etaleTopology B) AddCommGrpCat.{u + 1}) ℤ)
    (p : ℤ) :
    ((DerivedCategory.singleFunctor _ 0).obj
      ((freeYoneda.{u + 1} (SmoothSite.etaleTopology B)).obj X) ⟶
        (DerivedCategory.Q.obj K)⟦p⟧) →+
    ((DerivedCategory.singleFunctor _ 0).obj
      ((freeYoneda.{u + 1} X.left.smallEtaleTopology).obj (Etale.mk (𝟙 X.left))) ⟶
        (DerivedCategory.Q.obj
          (((fullSmallEtaleRestrict X).mapHomologicalComplex (.up ℤ)).obj K))⟦p⟧) := by
  let V : EtaleSeparatedFiniteType X.left :=
    MorphismProperty.Over.mk ⊤ (𝟙 X.left) (etaleSeparatedFiniteType.id_mem X.left)
  let g : (toSmoothSite X).obj V ⟶ X := SmoothSite.homMk (𝟙 X.left) (by rfl)
  exact
    { toFun := fun f ↦
        (DerivedCategory.singleFunctor _ 0).map
          ((freeYoneda.{u + 1} X.left.smallEtaleTopology).map
            (toSmallEtaleIdentityIso X.left).inv) ≫
        fullSmallDerivedHomMap X V K p
          ((DerivedCategory.singleFunctor _ 0).map
            ((freeYoneda.{u + 1} (SmoothSite.etaleTopology B)).map g) ≫ f)
      map_zero' := by simp
      map_add' := by intro f h; simp only [Preadditive.comp_add, map_add] }

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
