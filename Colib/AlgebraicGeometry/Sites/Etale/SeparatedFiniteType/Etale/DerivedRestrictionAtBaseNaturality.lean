/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Etale.DerivedRestrictionAtBase

/-! # Coefficient naturality at the actual identity neighborhood -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme SmoothSite
open AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open Stacks.Cohomology.FreeYonedaUnivLE
universe u wN wE wS
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

/-- Restriction at the original identity neighborhood preserves coefficient postcomposition. -/
lemma fullSmallDerivedHomMapAtBase_coefficient {B : Scheme.{u}} [IsAffine B]
    (X : SmoothSite B)
    [HasDerivedCategory.{wE} (Sheaf (SmoothSite.etaleTopology B) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{wS} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})]
    {K L : CochainComplex (Sheaf (SmoothSite.etaleTopology B) AddCommGrpCat.{u + 1}) ℤ}
    (g : K ⟶ L) (p : ℤ)
    (f : (DerivedCategory.singleFunctor _ 0).obj
      ((freeYoneda.{u + 1} (SmoothSite.etaleTopology B)).obj X) ⟶
        (DerivedCategory.Q.obj K)⟦p⟧) :
    fullSmallDerivedHomMapAtBase X L p (f ≫ (DerivedCategory.Q.map g)⟦p⟧') =
      fullSmallDerivedHomMapAtBase X K p f ≫
        (DerivedCategory.Q.map
          (((fullSmallEtaleRestrict X).mapHomologicalComplex (.up ℤ)).map g))⟦p⟧' := by
  simp only [fullSmallDerivedHomMapAtBase, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [← Category.assoc, fullSmallDerivedHomMap_coefficient, Category.assoc]

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

