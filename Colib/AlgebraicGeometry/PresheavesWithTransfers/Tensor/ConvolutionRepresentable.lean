/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ConvolutionParameter
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.Representable

/-!
# The tensor coend on two representables

First evaluate the represented right parameter, then use additive Yoneda
for the represented left coefficient. The composite takes a pure
generator to postcomposition with the original signed correspondence
product.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]
variable (F : Cor k ⥤ Cor k ⥤ Cor k) [F.Additive] [∀ X, (F.obj X).Additive]

local notation "R(" K ", " X ")" => Functor.obj (representableLarge K) X

local instance (T : Cor k) : (F.flip.obj T).Additive where
  map_add := by
    intro X Y f g
    change (F.map (f + g)).app T = (F.map f).app T + (F.map g).app T
    exact NatTrans.congr_app (F.map_add (f := f) (g := g)) T

/-- Convolution on two original representables represents the signed correspondence product. -/
def convolutionRepresentableIso (X Y : Cor k) :
    ((convolutionBifunctor F).obj (R(k, X))).obj (R(k, Y)) ≅ R(k, (F.obj X).obj Y) :=
  convolutionParameterIso F Y (R(k, X)) ≪≫ coendPushforwardRepresentableIso (F.flip.obj Y) X

/-- The represented comparison acts by composition with the original signed correspondence maps. -/
theorem convolutionRepresentableIso_hom_generator (X Y U V W : Cor k)
    (b : V ⟶ X) (c : W ⟶ Y) (a : U ⟶ (F.obj V).obj W) :
    (convolutionRepresentableIso F X Y).hom.hom.app (op U)
      (convolutionGenerator F (R(k, X)) (R(k, Y)) U V W (ULift.up b) (ULift.up c) a) =
        ULift.up (a ≫ convolutionCorrespondenceMap F b c) := by
  let H := coendPushforwardRepresentableHom (F.flip.obj Y) X
  let h := (convolutionParameterIso F Y (R(k, X))).hom
  let z := convolutionGenerator F (R(k, X)) (R(k, Y)) U V W (ULift.up b) (ULift.up c) a
  change H.hom.app (op U) (h.hom.app (op U) z) = _
  have h₁ := convolutionParameterIso_hom_generator F Y (R(k, X)) U V W (ULift.up b) c a
  have h₂ := coendPushforwardRepresentableHom_app (F.flip.obj Y) X U V b
    (a ≫ (F.obj V).map c)
  have h₃ : (a ≫ (F.obj V).map c) ≫ (F.flip.obj Y).map b =
      a ≫ convolutionCorrespondenceMap F b c :=
    (Category.assoc _ _ _).trans (congrArg (a ≫ ·) ((F.map b).naturality c))
  exact (congrArg (H.hom.app (op U)) h₁).trans (h₂.trans (congrArg ULift.up h₃))

set_option maxHeartbeats 700000 in
-- The generator calculation compares the bundled additive representables and the integral coend.
/-- The represented product comparison commutes with the original correspondences. -/
theorem convolutionRepresentableIso_naturality {X X' Y Y' : Cor k}
    (f : X ⟶ Y) (g : X' ⟶ Y') :
    convolutionMap F ((representableLarge k).map f) ((representableLarge k).map g) ≫
        (convolutionRepresentableIso F Y Y').hom =
      (convolutionRepresentableIso F X X').hom ≫
        (representableLarge k).map (convolutionCorrespondenceMap F f g) := by
  apply convolutionPresheaf_hom_ext
  intro U V W b c a
  change ULift.{u + 1} (V ⟶ X) at b
  change ULift.{u + 1} (W ⟶ X') at c
  obtain ⟨b⟩ := b
  obtain ⟨c⟩ := c
  let e := (convolutionRepresentableIso F Y Y').hom
  let e₀ := (convolutionRepresentableIso F X X').hom
  let r := (representableLarge k).map (convolutionCorrespondenceMap F f g)
  let m := convolutionMap F ((representableLarge k).map f) ((representableLarge k).map g)
  let z := convolutionGenerator F (R(k, X)) (R(k, X')) U V W (ULift.up b) (ULift.up c) a
  change e.hom.app (op U) (m.hom.app (op U) z) =
    r.hom.app (op U) (e₀.hom.app (op U) z)
  have hm : m.hom.app (op U) z = convolutionGenerator F (R(k, Y)) (R(k, Y'))
      U V W (ULift.up (b ≫ f)) (ULift.up (c ≫ g)) a :=
    convolutionMap_generator F ((representableLarge k).map f) ((representableLarge k).map g)
      U V W (ULift.up b) (ULift.up c) a
  have he := convolutionRepresentableIso_hom_generator F Y Y' U V W (b ≫ f) (c ≫ g) a
  have he₀ := convolutionRepresentableIso_hom_generator F X X' U V W b c a
  have hr := representableLarge_map_app_apply k (convolutionCorrespondenceMap F f g)
    (a ≫ convolutionCorrespondenceMap F b c)
  let bf : (V, W) ⟶ (X, X') := (b, c)
  let fg : (X, X') ⟶ (Y, Y') := (f, g)
  have hcomp : convolutionCorrespondenceMap F (b ≫ f) (c ≫ g) =
      convolutionCorrespondenceMap F b c ≫ convolutionCorrespondenceMap F f g :=
    (Functor.uncurry.obj F).map_comp bf fg
  have h : a ≫ convolutionCorrespondenceMap F (b ≫ f) (c ≫ g) =
      (a ≫ convolutionCorrespondenceMap F b c) ≫ convolutionCorrespondenceMap F f g :=
    (congrArg (a ≫ ·) hcomp).trans (Category.assoc _ _ _).symm
  exact (congrArg (e.hom.app (op U)) hm).trans (he.trans
    ((congrArg ULift.up h).trans (hr.symm.trans (congrArg (r.hom.app (op U)) he₀).symm)))

/-- The convolution of signed representables is naturally the representable of their product. -/
def convolutionRepresentableNatIso :
    ((representableLarge k).prod (representableLarge k)) ⋙ convolutionFunctor F ≅
      Functor.uncurry.obj F ⋙ representableLarge k :=
  NatIso.ofComponents (fun X => convolutionRepresentableIso F X.1 X.2)
    (fun {_ _} f => convolutionRepresentableIso_naturality F f.1 f.2)

end AlgebraicGeometry.PresheafWithTransfers
