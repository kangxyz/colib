module

import Colib.AlgebraicGeometry.PresheavesWithTransfers.GraphRestriction
import Colib.AlgebraicGeometry.PresheavesWithTransfers.Yoneda

open AlgebraicGeometry CategoryTheory Opposite Stacks.Chow
open AlgebraicGeometry.PresheafWithTransfers

universe v u

noncomputable section

variable (k : Type u) [Field k]

-- The coefficient universe remains independent of the arbitrary ground field.
example : Category (PresheafWithTransfers.{v} k) := inferInstance

example : Preadditive (PresheafWithTransfers.{v} k) := inferInstance

example (P : PresheafWithTransfers.{v} k) :
    Functor.Additive P.obj := inferInstance

example : (PresheafWithTransfers.forget.{v} (k := k)).Full := inferInstance

example : (PresheafWithTransfers.forget.{v} (k := k)).Faithful := inferInstance

example : (toPresheaf.{v} k).Additive := inferInstance

example : (toPresheaf.{v} k).Faithful := inferInstance

example (P : PresheafWithTransfers.{v} k) {X Y Z : Cor k}
    (α : X ⟶ Y) (β : Y ⟶ Z) :
    transfer P (incidenceTorPairing X.toSmoothSite.hom Y.toSmoothSite.hom
      Z.toSmoothSite.hom α β) = transfer P β ≫ transfer P α :=
  transfer_comp P α β

example (P : PresheafWithTransfers.{v} k) {X Y : Cor k}
    (n : ℤ) (α β : X ⟶ Y) :
    transfer P (n • α - β) = n • transfer P α - transfer P β := by
  rw [transfer_sub, transfer_zsmul]

example {P Q : PresheafWithTransfers.{v} k} (η : P ⟶ Q)
    {X Y : Cor k} (α : X ⟶ Y) :
    transfer P α ≫ η.hom.app (op X) = η.hom.app (op Y) ≫ transfer Q α :=
  transfer_naturality η α

example (P : PresheafWithTransfers.{v} k)
    {X Y : Scheme.SmoothSite (Spec (.of k))} (f : X ⟶ Y) :
    ((toPresheaf k).obj P).map f.op =
      transfer P (graphCorrespondenceOfComponents X.hom Y.hom f.left
        (MorphismProperty.Over.w f) (Cor.finite_genericPoints k (Cor.mk X))) := rfl

example (P : PresheafWithTransfers.{v} k) :
    (toPresheaf k).obj P = (Cor.graphFunctor k).op ⋙ P.obj := rfl

example : (representable k).Full := inferInstance

example : (representable k).Faithful := inferInstance

example : (representable k).Additive := inferInstance

example (X Y : Cor k) :
    sections ((representable k).obj X) Y =
      AddCommGrpCat.of (finiteCorrespondences Y.toSmoothSite.hom X.toSmoothSite.hom) :=
  representable_sections k X Y

example {X Y Z : Cor k} (α : Y ⟶ Z) (β : Z ⟶ X) :
    transfer ((representable k).obj X) α β =
      incidenceTorPairing Y.toSmoothSite.hom Z.toSmoothSite.hom X.toSmoothSite.hom α β := rfl

example {X Y Z : Cor k} (α : X ⟶ Y) (β : Z ⟶ X) :
    ((representable k).map α).hom.app (op Z) β =
      incidenceTorPairing Z.toSmoothSite.hom X.toSmoothSite.hom Y.toSmoothSite.hom β α := rfl

example : representable k ⋙ PresheafWithTransfers.forget = preadditiveYoneda :=
  representable_comp_forget k

example (P : PresheafWithTransfers.{u} k) (X : Cor k) (s : sections P X) :
    yonedaAddEquiv P X (sectionHom P X s) = s :=
  (yonedaAddEquiv P X).apply_symm_apply s

example (P : PresheafWithTransfers.{u} k) (X : Cor k)
    (η : (representable k).obj X ⟶ P) :
    sectionHom P X (yonedaAddEquiv P X η) = η :=
  (yonedaAddEquiv P X).symm_apply_apply η

example (P : PresheafWithTransfers.{u} k) (X : Cor k)
    (η θ : (representable k).obj X ⟶ P) :
    yonedaAddEquiv P X (η + θ) = yonedaAddEquiv P X η + yonedaAddEquiv P X θ :=
  (yonedaAddEquiv P X).map_add η θ

example (P : PresheafWithTransfers.{u} k) {X Y : Cor k} (α : X ⟶ Y)
    (f : (representable k).obj Y ⟶ P) :
    yonedaAddEquiv P X ((representable k).map α ≫ f) =
      transfer P α (yonedaAddEquiv P Y f) :=
  yonedaAddEquiv_naturality_left P α f
