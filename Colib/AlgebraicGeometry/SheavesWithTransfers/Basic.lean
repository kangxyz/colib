/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Topology
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.GraphRestriction

/-!
# Nisnevich sheaves with transfers

A sheaf with transfers is an actual additive presheaf on finite
correspondences whose restriction along the graph functor is a Nisnevich
sheaf on the smooth site. Morphisms retain naturality for all transfers.
Forgetting transfers gives a faithful additive functor to ordinary sheaves.

The definition works over an arbitrary field and includes disconnected and
empty smooth objects. It does not assert transfer-preserving sheafification
or sheafness of representable transfer presheaves.

Implementation adapted from `motivic_source_a6805c4`,
`Motivic/Transfers/Sheaf/Basic.lean`, blob
`d39611399e910279dabc882b0d7d9db754617bc7`. The original arbitrary-field scope and coefficient
universes are retained, using the actual native correspondence category.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe v u

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme

/-- The actual Nisnevich sheaf condition on the graph-restricted presheaf. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Transfers/Sheaf/Basic.lean: PresheafWithTransfers.IsNisnevichSheaf"
  "adaptation" "native Nisnevich sheaf condition after actual graph restriction"]
def PresheafWithTransfers.IsNisnevichSheaf (k : Type u) [Field k] :
    ObjectProperty (PresheafWithTransfers.{v} k) :=
  fun P ↦ Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
    ((PresheafWithTransfers.toPresheaf k).obj P)

/-- Additive presheaves with transfers whose underlying presheaves are Nisnevich sheaves. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Transfers/Sheaf/Basic.lean: SheafWithTransfers"
  "adaptation" "full subcategory defined by the native graph-restricted Nisnevich sheaf condition",
  colib_tag "COL-0369",
  colib_ref "motivic_source_a6805c4"
  "Motivic/Transfers/Sheaf/Basic.lean"
  "adaptation" "Ordinary Nisnevich sheaves with transfers"]
abbrev SheafWithTransfers (k : Type u) [Field k] :=
  (PresheafWithTransfers.IsNisnevichSheaf.{v} k).FullSubcategory

namespace SheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]

/-- Forget the sheaf condition, keeping every transfer and its naturality. -/
abbrev forget : SheafWithTransfers.{v} k ⥤ PresheafWithTransfers.{v} k :=
  (PresheafWithTransfers.IsNisnevichSheaf k).ι

/-- Forget transfers, retaining the actual underlying ordinary Nisnevich sheaf. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Transfers/Sheaf/Basic.lean: SheafWithTransfers.toSheaf"
  "adaptation" "faithful additive forgetful functor to actual ordinary Nisnevich sheaves"]
def toSheaf : SheafWithTransfers.{v} k ⥤
    Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{v} :=
  ObjectProperty.lift _ (forget k ⋙ PresheafWithTransfers.toPresheaf k)
    (fun P ↦ P.property)

instance : (toSheaf.{v} k).Faithful where
  map_injective {P Q η θ} h := by
    apply ObjectProperty.hom_ext
    apply (PresheafWithTransfers.toPresheaf k).map_injective
    exact congrArg (fun f ↦ f.hom) h

instance : (toSheaf.{v} k).Additive where
  map_add {P Q} η θ := by
    apply ObjectProperty.hom_ext
    exact (PresheafWithTransfers.toPresheaf k).map_add

/-- Forgetting the ordinary sheaf condition recovers exactly graph restriction. -/
def toSheafCompSheafToPresheafIso :
    toSheaf.{v} k ⋙ sheafToPresheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
      AddCommGrpCat.{v} ≅ forget k ⋙ PresheafWithTransfers.toPresheaf k := Iso.refl _

@[simp]
theorem toSheaf_obj_obj (P : SheafWithTransfers.{v} k)
    (X : (SmoothSite (Spec (.of k)))ᵒᵖ) :
    ((toSheaf k).obj P).obj.obj X =
      PresheafWithTransfers.sections P.obj (Cor.mk X.unop) := rfl

/-- Ordinary restrictions are transfers along the actual graph correspondence. -/
@[simp]
theorem toSheaf_obj_map (P : SheafWithTransfers.{v} k)
    {X Y : (SmoothSite (Spec (.of k)))ᵒᵖ} (f : X ⟶ Y) :
    ((toSheaf k).obj P).obj.map f =
      PresheafWithTransfers.transfer P.obj ((Cor.graphFunctor k).map f.unop) := rfl

@[simp]
theorem toSheaf_map_hom {P Q : SheafWithTransfers.{v} k} (η : P ⟶ Q) :
    ((toSheaf k).map η).hom = (PresheafWithTransfers.toPresheaf k).map η.hom := rfl

end SheafWithTransfers

end AlgebraicGeometry
