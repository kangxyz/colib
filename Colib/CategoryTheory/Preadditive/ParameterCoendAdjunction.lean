/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Preadditive.ParameterCoend
public import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Colib.CategoryTheory.Preadditive.AdditiveFunctorAbelian

/-!
# Additive pushforward on the original tensor coends

An additive functor on finite correspondences acts covariantly on action
presheaves by the existing tensor coend. This construction is left adjoint
to precomposition with the opposite functor. It uses the same integral
coefficient groups, signed correspondences and pure generators as
`presheaf` and imposes no geometric condition on a parameter.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory TensorProduct

universe u v w

namespace CategoryTheory.Preadditive.ParameterCoend

variable {C : Type u} [Category.{v} C] [Preadditive C]
open CategoryTheory.Preadditive.Convolution (integerModuleFunctor)

/-- The contravariant action of a bundled additive presheaf. -/
abbrev action (P : Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}) {X Y : C} (f : X ⟶ Y) :=
  P.obj.map f.op

private theorem action_zero (P : Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}) (X Y : C) :
    action P (0 : X ⟶ Y) = 0 := by simp [action]
private theorem action_add (P : Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}) {X Y : C} (f g :
    X ⟶ Y) :
    action P (f + g) = action P f + action P g := by simp [action]
private theorem action_comp (P : Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    action P (f ≫ g) = action P g ≫ action P f := by simp [action]
private theorem action_id (P : Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}) (X : C) :
    action P (𝟙 X) = 𝟙 _ := by simp [action]
private theorem action_naturality {P Q : Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}}
    (f : P ⟶ Q) {X Y : C} (a : X ⟶ Y) :
    action P a ≫ f.hom.app (op X) = f.hom.app (op Y) ≫ action Q a :=
  f.hom.naturality a.op

theorem presheaf_hom_ext (F : C ⥤ C)
    {P Q : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})}
    {f g : presheaf F P ⟶ Q}
    (h : ∀ (X Y : C) (s : (P.obj.obj (op Y))) (a : X ⟶ F.obj Y),
      f.hom.app (op X) (generator F P X Y s a) =
        g.hom.app (op X) (generator F P X Y s a)) : f = g := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext X
  let U := forget₂ (ModuleCat.{max u v w} ℤ) AddCommGrpCat.{max u v w}
  let M := sections F P X.unop
  let N := ModuleCat.of ℤ ((Q.obj.obj (op X.unop)))
  let φ : U.obj M ⟶ U.obj N := f.hom.app X
  let ψ : U.obj M ⟶ U.obj N := g.hom.app X
  have hfg : U.preimage φ = U.preimage ψ := by
    apply sections_hom_ext
    intro Y s a
    let z := generator F P X.unop Y s a
    exact (ConcreteCategory.congr_hom (U.map_preimage φ) z).trans
      ((h X.unop Y s a).trans (ConcreteCategory.congr_hom (U.map_preimage ψ) z).symm)
  change φ = ψ
  rw [← U.map_preimage φ, ← U.map_preimage ψ, hfg]

variable (F : C ⥤ C) [F.Additive]

/-- Restrict a action presheaf along an additive correspondence functor. -/
def additivePrecompose :
    (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}) ⥤ (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}) where
  obj P := AdditiveFunctor.of (F.op ⋙ P.obj)
  map η := ObjectProperty.homMk (Functor.whiskerLeft F.op η.hom)
  map_id _ := by
    apply ObjectProperty.hom_ext
    rfl
  map_comp _ _ := by
    apply ObjectProperty.hom_ext
    rfl

instance : (additivePrecompose F).Additive where
  map_add := by
    intro P Q f g
    apply ObjectProperty.hom_ext
    rfl

/-- The coefficient map for the parameter adjunction on a pure generator. -/
def coendPushforwardUnit (P : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})) :
    P ⟶ (additivePrecompose F).obj (presheaf F P) :=
  ObjectProperty.homMk
    { app X := by
        let W := (F).obj X.unop
        let j : ModuleCat.of ℤ ((P.obj.obj (op X.unop)) ⊗[ℤ] ULift.{max u v w} (W
    ⟶ W)) ⟶
            sections F P W := coend.ι (diagram F P W) X.unop
        let a : ULift.{max u v w} (W ⟶ W) := ULift.up (𝟙 W)
        change (P.obj.obj (op X.unop)) ⟶ AddCommGrpCat.of (sections F P W)
        exact AddCommGrpCat.ofHom
          { toFun := fun s => generator F P W X.unop s (𝟙 _)
            map_zero' := by
              change j ((0 : (P.obj.obj (op X.unop))) ⊗ₜ[ℤ] a) = 0
              rw [TensorProduct.zero_tmul, map_zero]
            map_add' := by
              intro s t
              change j ((s + t) ⊗ₜ[ℤ] a) = j (s ⊗ₜ[ℤ] a) + j (t ⊗ₜ[ℤ] a)
              rw [TensorProduct.add_tmul, map_add] }
      naturality X Y β := by
        apply AddCommGrpCat.ext
        intro s
        change generator F P ((F).obj Y.unop) Y.unop (action P β.unop s) (𝟙 _) =
          transfer F P ((F).map β.unop)
            (generator F P ((F).obj X.unop) X.unop s (𝟙 _))
        rw [transfer_generator, Category.comp_id, generator_transfer,
          Category.id_comp] }

theorem coendPushforwardUnit_app_apply (P : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}))
    (X : C) (s : (P.obj.obj (op X))) :
    (coendPushforwardUnit F P).hom.app (op X) s =
      generator F P ((F).obj X) X s (𝟙 _) := rfl


variable {P Q : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})}

/-- Evaluate the actual signed action against the value of a coefficient map. -/
def coendPushforwardPairing (θ : P ⟶ (additivePrecompose F).obj Q) (X Y : C) :
    ((diagram F P X).obj (op Y)).obj Y ⟶
      ModuleCat.of ℤ ((Q.obj.obj (op X))) := by
  let h : (P.obj.obj (op Y)) ⟶ (Q.obj.obj (op (F.obj Y))) := θ.hom.app (op Y)
  let ev (s : (P.obj.obj (op Y))) : ULift.{max u v w} (X ⟶ (F).obj Y) →+ (Q.obj.obj
    (op X)) :=
    { toFun := fun a => action Q a.down (h s)
      map_zero' := by rw [show (0 : ULift.{max u v w} (X ⟶ (F).obj Y)).down = 0 from rfl,
        action_zero]; rfl
      map_add' a b := by
        change action Q (a.down + b.down) _ = _
        rw [action_add]
        rfl }
  let e : (P.obj.obj (op Y)) →+ (ULift.{max u v w} (X ⟶ (F).obj Y) →ₗ[ℤ]
    (Q.obj.obj (op X))) :=
    { toFun := fun s => (ev s).toIntLinearMap
      map_zero' := by
        ext a
        change action Q a.down (h 0) = 0
        rw [map_zero, map_zero]
      map_add' s t := by
        ext a
        change action Q a.down (h (s + t)) =
          action Q a.down (h s) + action Q a.down (h t)
        rw [map_add, map_add] }
  exact ModuleCat.ofHom (TensorProduct.lift e.toIntLinearMap)

@[simp]
theorem coendPushforwardPairing_tmul (θ : P ⟶ (additivePrecompose F).obj Q) (X Y : C)
    (s : (P.obj.obj (op Y))) (a : ULift.{max u v w} (X ⟶ (F).obj Y)) :
    coendPushforwardPairing F θ X Y (s ⊗ₜ[ℤ] a) = action Q a.down (θ.hom.app (op
    Y) s) := rfl

/-- The action pairing identifies the two maps in the coend relation. -/
theorem coendPushforwardPairing_dinatural (θ : P ⟶ (additivePrecompose F).obj Q)
    (X : C) {Y Z : C} (f : Y ⟶ Z) :
    ((diagram F P X).map f.op).app Y ≫ coendPushforwardPairing F θ X Y =
      ((diagram F P X).obj (op Z)).map f ≫ coendPushforwardPairing F θ X Z := by
  let A := P.obj ⋙ integerModuleFunctor
  let B := homModule F X
  change (A.map f.op ⊗ₘ B.map (𝟙 Y)) ≫ coendPushforwardPairing F θ X Y =
    (A.map (𝟙 (op Z)) ⊗ₘ B.map f) ≫ coendPushforwardPairing F θ X Z
  rw [A.map_id, B.map_id]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro s a
  change ULift.{max u v w} (X ⟶ (F).obj Y) at a
  have h := ConcreteCategory.congr_hom (action_naturality θ f) s
  change θ.hom.app (op Y) (action P f s) =
    action Q ((F).map f) (θ.hom.app (op Z) s) at h
  change action Q a.down (θ.hom.app (op Y) (action P f s)) =
    action Q (a.down ≫ (F).map f) (θ.hom.app (op Z) s)
  rw [h, action_comp]
  rfl

/-- The native coend map induced by the action pairing. -/
def coendPushforwardDescApp (θ : P ⟶ (additivePrecompose F).obj Q) (X : C) :
    sections F P X ⟶ ModuleCat.of ℤ ((Q.obj.obj (op X))) :=
  coend.desc («F» := diagram F P X) (coendPushforwardPairing F θ X)
    (fun _ _ f => coendPushforwardPairing_dinatural F θ X f)

/-- On every generator the coend map is the actual signed action. -/
@[simp]
theorem coendPushforwardDescApp_generator (θ : P ⟶ (additivePrecompose F).obj Q) (X Y : C)
    (s : (P.obj.obj (op Y))) (a : X ⟶ (F).obj Y) :
    coendPushforwardDescApp F θ X (generator F P X Y s a) =
      action Q a (θ.hom.app (op Y) s) := by
  change (coend.ι (diagram F P X) Y ≫
    coendPushforwardDescApp F θ X) (s ⊗ₜ[ℤ] ULift.up a) = _
  rw [coendPushforwardDescApp, coend.ι_desc]
  exact coendPushforwardPairing_tmul F θ X Y s (ULift.up a)

/-- Evaluation from the coend commutes with every actual source correspondence. -/
@[reassoc]
theorem coendPushforwardDescApp_naturality (θ : P ⟶ (additivePrecompose F).obj Q)
    {X X' : C} (β : X' ⟶ X) :
    transfer F P β ≫ coendPushforwardDescApp F θ X' =
      coendPushforwardDescApp F θ X ≫ integerModuleFunctor.map (action Q β) := by
  apply sections_hom_ext
  intro Y s a
  change coendPushforwardDescApp F θ X' (transfer F P β
    (generator F P X Y s a)) =
      action Q β (coendPushforwardDescApp F θ X (generator F P X Y s a))
  rw [transfer_generator, coendPushforwardDescApp_generator,
    coendPushforwardDescApp_generator, action_comp]
  rfl

/-- Descend the original coefficient pairing as a morphism with transfers. -/
def coendPushforwardDesc (θ : P ⟶ (additivePrecompose F).obj Q) : presheaf F P ⟶ Q :=
  ObjectProperty.homMk
    { app X := (forget₂ (ModuleCat ℤ) AddCommGrpCat).map (coendPushforwardDescApp F
    θ X.unop)
      naturality X Y β := by
        let U := forget₂ (ModuleCat.{max u v w} ℤ) AddCommGrpCat.{max u v w}
        change U.map (transfer F P β.unop) ≫
          U.map (coendPushforwardDescApp F θ Y.unop) =
          U.map (coendPushforwardDescApp F θ X.unop) ≫
            U.map (integerModuleFunctor.map (action Q β.unop))
        exact (U.map_comp _ _).symm.trans
          ((congrArg (fun f => U.map f) (coendPushforwardDescApp_naturality F θ
    β.unop)).trans
            (U.map_comp _ _)) }

@[simp]
theorem coendPushforwardDesc_app_generator (θ : P ⟶ (additivePrecompose F).obj Q) (X Y : C)
    (s : (P.obj.obj (op Y))) (a : X ⟶ (F).obj Y) :
    (coendPushforwardDesc F θ).hom.app (op X) (generator F P X Y s a) =
      action Q a (θ.hom.app (op Y) s) :=
  coendPushforwardDescApp_generator F θ X Y s a


/-- The adjunction bijection, with the specified action and unit formulas. -/
def coendPushforwardHomEquiv (P Q : ((Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}))) :
    (presheaf F P ⟶ Q) ≃ (P ⟶ (additivePrecompose F).obj Q) where
  toFun f := coendPushforwardUnit F P ≫ (additivePrecompose F).map f
  invFun := coendPushforwardDesc F
  left_inv f := by
    apply presheaf_hom_ext
    intro X Y s a
    rw [coendPushforwardDesc_app_generator]
    let z := generator F P ((F).obj Y) Y s (𝟙 _)
    change action Q a (f.hom.app (op ((F).obj Y)) z) =
      f.hom.app (op X) (generator F P X Y s a)
    have h := ConcreteCategory.congr_hom (action_naturality f a) z
    change f.hom.app (op X) (transfer F P a z) =
      action Q a (f.hom.app (op ((F).obj Y)) z) at h
    rw [show z = generator F P ((F).obj Y) Y s (𝟙 _) from rfl,
      transfer_generator, Category.comp_id] at h
    exact h.symm
  right_inv θ := by
    apply ObjectProperty.hom_ext
    ext X s
    change (coendPushforwardDesc F θ).hom.app (op ((F).obj X.unop))
      (generator F P ((F).obj X.unop) X.unop s (𝟙 _)) = θ.hom.app X s
    rw [coendPushforwardDesc_app_generator, action_id]
    rfl

/-- The parameter adjunction acts by the original coefficient maps on the right. -/
theorem coendPushforwardHomEquiv_naturality_right (P Q Q' : (Cᵒᵖ ⥤+
    AddCommGrpCat.{max u v w}))
    (g : Q ⟶ Q') (f : presheaf F P ⟶ Q) :
    coendPushforwardHomEquiv F P Q' (f ≫ g) =
      coendPushforwardHomEquiv F P Q f ≫
        (additivePrecompose F :
          (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}) ⥤ (Cᵒᵖ ⥤+ AddCommGrpCat.{max u
    v w})).map g := by
  let R : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}) ⥤ (Cᵒᵖ ⥤+ AddCommGrpCat.{max u
    v w}) :=
    additivePrecompose F
  let η : P ⟶ R.obj (presheaf F P) := coendPushforwardUnit F P
  change η ≫ R.map (f ≫ g) = (η ≫ R.map f) ≫ R.map g
  exact (congrArg (fun h => η ≫ h) (R.map_comp f g)).trans
    (Category.assoc η (R.map f) (R.map g)).symm

/-- Tensoring with the parameter is left adjoint to its original section functor. -/
def coendPushforward : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}) ⥤ (Cᵒᵖ ⥤+
    AddCommGrpCat.{max u v w}) :=
  Adjunction.leftAdjointOfEquiv
    (G := (additivePrecompose F :
      (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}) ⥤ (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})))
    (F_obj := presheaf F) (coendPushforwardHomEquiv F)
    (coendPushforwardHomEquiv_naturality_right F)

/-- The adjunction on the original action categories. -/
def coendPushforwardAdjunction :
    coendPushforward F ⊣ (additivePrecompose F :
      (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}) ⥤ (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})) :=
  Adjunction.adjunctionOfEquivLeft
    (G := (additivePrecompose F :
      (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}) ⥤ (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})))
    (F_obj := presheaf F) (coendPushforwardHomEquiv F)
    (coendPushforwardHomEquiv_naturality_right F)

instance : (coendPushforward F).IsLeftAdjoint :=
  (coendPushforwardAdjunction F).isLeftAdjoint

instance : (coendPushforward F).Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts (coendPushforward F)
  exact Functor.additive_of_preservesBinaryBiproducts (coendPushforward F)

/-- The actual adjunction unit is the original pure-tensor map. -/
@[simp]
theorem coendPushforwardAdjunction_unit_app (P : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})) :
    (coendPushforwardAdjunction F).unit.app P = coendPushforwardUnit F P := by
  let R : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}) ⥤ (Cᵒᵖ ⥤+ AddCommGrpCat.{max u
    v w}) :=
    additivePrecompose F
  let η : P ⟶ R.obj (presheaf F P) := coendPushforwardUnit F P
  change η ≫ R.map (𝟙 (presheaf F P)) = η
  rw [R.map_id, Category.comp_id]


end CategoryTheory.Preadditive.ParameterCoend
