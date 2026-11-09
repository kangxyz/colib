module

import Colib.AlgebraicGeometry.SheavesWithTransfers.Basic

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme

universe v u

noncomputable section

variable (k : Type u) [Field k]

-- This tests the actual full subcategory, with no representable-sheafness assumption.
example : Category (SheafWithTransfers.{v} k) := inferInstance

example : Preadditive (SheafWithTransfers.{v} k) := inferInstance

example (P : PresheafWithTransfers.{v} k) :
    PresheafWithTransfers.IsNisnevichSheaf k P ↔
      Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
        ((PresheafWithTransfers.toPresheaf k).obj P) := Iff.rfl

example (P : PresheafWithTransfers.{v} k)
    (hP : Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((PresheafWithTransfers.toPresheaf k).obj P)) :
    SheafWithTransfers.{v} k := ⟨P, hP⟩

example : (SheafWithTransfers.forget.{v} k).Full := inferInstance

example : (SheafWithTransfers.forget.{v} k).Faithful := inferInstance

example : (SheafWithTransfers.forget.{v} k).Additive := inferInstance

example : (SheafWithTransfers.toSheaf.{v} k).Faithful := inferInstance

example : (SheafWithTransfers.toSheaf.{v} k).Additive := inferInstance

example (P : SheafWithTransfers.{v} k) :
    Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((PresheafWithTransfers.toPresheaf k).obj P.obj) := P.property

example : SheafWithTransfers.toSheaf.{v} k ⋙
    sheafToPresheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{v} =
      SheafWithTransfers.forget k ⋙ PresheafWithTransfers.toPresheaf k := rfl

example (P : SheafWithTransfers.{v} k) (X : SmoothSite (Spec (.of k))) :
    ((SheafWithTransfers.toSheaf k).obj P).obj.obj (op X) =
      PresheafWithTransfers.sections P.obj (Cor.mk X) := rfl

example (P : SheafWithTransfers.{v} k) {X Y : SmoothSite (Spec (.of k))}
    (f : X ⟶ Y) :
    ((SheafWithTransfers.toSheaf k).obj P).obj.map f.op =
      PresheafWithTransfers.transfer P.obj ((Cor.graphFunctor k).map f) := rfl

example {P Q : SheafWithTransfers.{v} k} (η : P ⟶ Q) (X : Cor k) :
    ((SheafWithTransfers.toSheaf k).map η).hom.app (op X.toSmoothSite) =
      η.hom.hom.app (op X) := rfl

example {P Q : SheafWithTransfers.{v} k} (η θ : P ⟶ Q)
    (h : (SheafWithTransfers.toSheaf k).map η = (SheafWithTransfers.toSheaf k).map θ) :
    η = θ := (SheafWithTransfers.toSheaf k).map_injective h
