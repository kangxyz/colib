/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Original.MapAtBase

/-! # Explicit transport of the genuine edge back to the original cohomology map -/
/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
https://github.com/kangxyz/motivic/blob/a6805c4a87cdfd7717dd7a94039246a167f15380/Motivic/Aglib/AlgebraicGeometry/Sites/Etale/SeparatedFiniteType/Cohomology/Original/MapTransport.lean
Source blob `3f9dbfe73b9f111c65abda783f00140a6cfafb0e`.
Native mathematical objects, original coefficient universes, and actual displayed maps are retained.

-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open Stacks.Cohomology.FreeYonedaUnivLE
variable {B : Scheme.{u}} {X Y : SmoothSite B} (h : Y ⟶ X)
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (nisnevichTopology X.left) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (nisnevichTopology Y.left) AddCommGrpCat.{u + 1})]

/-- The coefficient-map/edge composite, transported back, is exactly the original map. -/
theorem originalRestriction_eq_transported_ordinaryEdgeMap
    (F : Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1})
    (n : ℕ) (x : Abelian.Ext.{u + 1}
      ((freeYoneda.{u + 1} (SmoothSite.nisnevichTopology B)).obj X) F n) :
    (cohomologyPresheaf.{u + 1, u + 1} F n).map h.op x =
      (cohomologyAtBaseEquiv Y F n).symm
        ((cohomologyPresheaf.{u + 1, u + 1}
          ((restrict Y AddCommGrpCat).obj F) n).map (baseChangeIdentityIso h).inv.op
          (ordinaryEdgeMap h.left (identityObject X) ((restrict Y AddCommGrpCat).obj F) n
            (((cohomologyPresheafFunctor (nisnevichTopology X.left) n).map
              (restrictionToDirectImage F h)).app (op (identityObject X))
                (cohomologyAtBaseEquiv X F n x)))) := by
  apply (cohomologyAtBaseEquiv Y F n).injective
  rw [AddEquiv.apply_symm_apply, ordinaryEdgeMap_atBase_originalRestriction]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    Iso.inv_hom_id, op_id, CategoryTheory.Functor.map_id]
  rfl

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
