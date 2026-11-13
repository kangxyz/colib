/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Contraction

/-!
# Torus sections on Nisnevich sheaves with transfers

The native torus product reindexes the original transfer presheaf. The
existing continuity proof gives a sheaf with the same signed transfers
and the same restrictions at every smooth object.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme

universe u v

namespace AlgebraicGeometry.SheafWithTransfers

open AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "Gₘ" => SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k))

/-- Evaluate on the actual product with the multiplicative group, keeping transfers. -/
def torusSectionsFunctor : SheafWithTransfers.{v} k ⥤ SheafWithTransfers.{v} k where
  obj F := ⟨torusSections F.obj, withParameter_isNisnevichSheaf F.obj F.property Gₘ⟩
  map f := ObjectProperty.homMk (withParameterMap f.hom Gₘ)
  map_id F := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    rfl

/-- The underlying coefficient is exactly the already chosen torus reindexing. -/
@[simp]
theorem torusSectionsFunctor_obj_obj (F : SheafWithTransfers.{v} k) :
    ((torusSectionsFunctor k).obj F).obj = torusSections F.obj := rfl

/-- The coefficient maps are evaluated on the original signed products. -/
@[simp]
theorem torusSectionsFunctor_map_hom {F G : SheafWithTransfers.{v} k} (f : F ⟶ G) :
    ((torusSectionsFunctor k).map f).hom = withParameterMap f.hom Gₘ := rfl

instance : (torusSectionsFunctor k : SheafWithTransfers.{v} k ⥤
    SheafWithTransfers.{v} k).Additive where
  map_add := by
    intro F G f g
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    rfl

end AlgebraicGeometry.SheafWithTransfers
