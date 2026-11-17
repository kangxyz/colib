/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Preadditive.ParameterCoendAdjunction
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Identity and isomorphism comparison for additive parameter coends -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace CategoryTheory.Preadditive.ParameterCoend

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (F : C ⥤ C) [F.Additive]

/-- An isomorphism of additive parameter functors identifies their restriction functors. -/
def additivePrecomposeNatIso {G : C ⥤ C} [G.Additive] (e : F ≅ G) :
    additivePrecompose F ≅ additivePrecompose G :=
  let D := additiveFunctor (C)ᵒᵖ AddCommGrpCat.{max u v w}
  let d : F.op ≅ G.op := (NatIso.op e).symm
  let a (P : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})) :
      (additivePrecompose F).obj P ≅ (additivePrecompose G).obj P :=
    ObjectProperty.isoMk D (Functor.isoWhiskerRight d P.obj)
  NatIso.ofComponents a (fun {P Q} f => by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    change f.hom.app (F.op.obj X) ≫ Q.obj.map (d.hom.app X) =
      P.obj.map (d.hom.app X) ≫ f.hom.app (G.op.obj X)
    exact (f.hom.naturality (d.hom.app X)).symm)

/-- The adjunctions transport pushforward along an isomorphism of parameter functors. -/
def coendPushforwardNatIso {G : C ⥤ C} [G.Additive] (e : F ≅ G) :
    coendPushforward F ≅ coendPushforward G :=
  ((coendPushforwardAdjunction F).ofNatIsoRight (additivePrecomposeNatIso F e)).leftAdjointUniq
    (coendPushforwardAdjunction G)

/-- Restriction along the identity correspondence functor is the identity on presheaves. -/
def additivePrecomposeIdIso : additivePrecompose (𝟭 (C)) ≅ 𝟭 ((Cᵒᵖ ⥤+
    AddCommGrpCat.{max u v w})) :=
  NatIso.ofComponents
    (fun P => ObjectProperty.isoMk _ P.obj.leftUnitor)
    (fun f => by
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext X
      change f.hom.app X ≫ 𝟙 _ = 𝟙 _ ≫ f.hom.app X
      rw [Category.comp_id, Category.id_comp])

/-- The native coend pushforward along the identity is the identity functor. -/
def coendPushforwardIdIso : coendPushforward (𝟭 (C)) ≅ 𝟭 ((Cᵒᵖ ⥤+
    AddCommGrpCat.{max u v w})) :=
  ((coendPushforwardAdjunction (𝟭 (C))).ofNatIsoRight
      (additivePrecomposeIdIso (C := C))).leftAdjointUniq Adjunction.id

/-- A parameter naturally isomorphic to the identity has identity additive coend
    pushforward. -/
def coendPushforwardUnitor (e : F ≅ 𝟭 C) :
    coendPushforward F ≅ 𝟭 (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}) :=
  coendPushforwardNatIso F e ≪≫ coendPushforwardIdIso

end CategoryTheory.Preadditive.ParameterCoend
