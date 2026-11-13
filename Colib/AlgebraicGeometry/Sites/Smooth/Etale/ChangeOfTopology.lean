/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.Topology
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Sites.Abelian

/-!
# Ordinary change from the Nisnevich to the étale topology

On the same smooth category, étale sheafification of the underlying Nisnevich
sheaf is left adjoint to the literal restriction of étale sheaves. The unit and
counit are the native sheafification maps. This construction concerns ordinary
sheaves, not transfers or derived comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Scheme.SmoothSite

variable (S : Scheme.{u}) (A : Type v) [Category.{w} A]

/-- Étale sheafification of the underlying Nisnevich sheaf on the same smooth site. -/
def nisnevichToEtaleSheaf [HasWeakSheafify (etaleTopology S) A] :
    Sheaf (nisnevichTopology S) A ⥤ Sheaf (etaleTopology S) A :=
  sheafToPresheaf (nisnevichTopology S) A ⋙ presheafToSheaf (etaleTopology S) A

/-- Ordinary change of topology is the restriction of the native sheafification adjunction. -/
@[colib_tag "COL-1208",
  colib_ref "mathlib_stable_localization_pin"
    "Mathlib/CategoryTheory/Adjunction/Restrict.lean:42-58" "specialization"
    "Restrict native sheafification to Nisnevich sheaves on the same smooth category"]
def nisnevichToEtaleSheafAdjunction [HasWeakSheafify (etaleTopology S) A] :
    nisnevichToEtaleSheaf S A ⊣ etaleToNisnevichSheaf S A :=
  (sheafificationAdjunction (etaleTopology S) A).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf (nisnevichTopology S) A)
    (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

instance [HasWeakSheafify (etaleTopology S) A] :
    (nisnevichToEtaleSheaf S A).IsLeftAdjoint :=
  (nisnevichToEtaleSheafAdjunction S A).isLeftAdjoint

instance [HasWeakSheafify (etaleTopology S) A] :
    (etaleToNisnevichSheaf S A).IsRightAdjoint :=
  (nisnevichToEtaleSheafAdjunction S A).isRightAdjoint

@[simp]
theorem nisnevichToEtaleSheaf_obj_obj [HasWeakSheafify (etaleTopology S) A]
    (F : Sheaf (nisnevichTopology S) A) :
    ((nisnevichToEtaleSheaf S A).obj F).obj = sheafify (etaleTopology S) F.obj := rfl

@[simp]
theorem nisnevichToEtaleSheaf_map_hom [HasWeakSheafify (etaleTopology S) A]
    {F G : Sheaf (nisnevichTopology S) A} (f : F ⟶ G) :
    ((nisnevichToEtaleSheaf S A).map f).hom = sheafifyMap (etaleTopology S) f.hom := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The unit is the canonical map to actual étale sheafification. -/
@[simp]
theorem nisnevichToEtaleSheafAdjunction_unit_app_hom
    [HasWeakSheafify (etaleTopology S) A] (F : Sheaf (nisnevichTopology S) A) :
    ((nisnevichToEtaleSheafAdjunction S A).unit.app F).hom =
      toSheafify (etaleTopology S) F.obj := by
  change (sheafToPresheaf _ _).map ((nisnevichToEtaleSheafAdjunction S A).unit.app F) = _
  simp only [nisnevichToEtaleSheafAdjunction,
    Adjunction.map_restrictFullyFaithful_unit_app, Iso.refl_hom, NatTrans.id_app,
    sheafificationAdjunction_unit_app]
  dsimp
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The counit is the unique native sheafification lift of the identity. -/
@[simp]
theorem nisnevichToEtaleSheafAdjunction_counit_app_hom
    [HasWeakSheafify (etaleTopology S) A] (F : Sheaf (etaleTopology S) A) :
    ((nisnevichToEtaleSheafAdjunction S A).counit.app F).hom =
      sheafifyLift (etaleTopology S) (𝟙 F.obj) F.property := by
  have h := Adjunction.map_restrictFullyFaithful_counit_app
    (sheafificationAdjunction (etaleTopology S) A)
    (fullyFaithfulSheafToPresheaf (nisnevichTopology S) A)
    (Functor.FullyFaithful.id _) (L := nisnevichToEtaleSheaf S A)
    (R := etaleToNisnevichSheaf S A) (Iso.refl _) (Iso.refl _) F
  apply (congrArg (fun f ↦ f.hom) h).trans
  change ((𝟙 _ ≫ (presheafToSheaf (etaleTopology S) A).map (𝟙 _) ≫
    (sheafificationAdjunction (etaleTopology S) A).counit.app F)).hom = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
  exact sheafificationAdjunction_counit_app_val (etaleTopology S) F

/-- Restricting an étale sheaf and sheafifying it again has the canonical counit isomorphism. -/
instance [HasWeakSheafify (etaleTopology S) A] :
    IsIso (nisnevichToEtaleSheafAdjunction S A).counit := inferInstance

instance [HasWeakSheafify (etaleTopology S) A] :
    PreservesFiniteColimits (nisnevichToEtaleSheaf S A) := inferInstance

instance [HasFiniteLimits A] [HasSheafify (etaleTopology S) A] :
    PreservesFiniteLimits (nisnevichToEtaleSheaf S A) := by
  unfold nisnevichToEtaleSheaf
  infer_instance

instance [Abelian A] [HasSheafify (etaleTopology S) A] :
    (nisnevichToEtaleSheaf S A).Additive := by
  unfold nisnevichToEtaleSheaf
  infer_instance

end AlgebraicGeometry.Scheme.SmoothSite
