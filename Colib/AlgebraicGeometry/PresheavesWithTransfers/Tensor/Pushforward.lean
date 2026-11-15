/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ParameterTensor.Adjunction
public import Colib.CategoryTheory.Preadditive.AdditiveFunctorAbelian

/-!
# Additive pushforward on the original tensor coends

An additive functor on finite correspondences acts covariantly on transfer
presheaves by the existing tensor coend. This construction is left adjoint
to precomposition with the opposite functor. It uses the same integral
coefficient groups, signed correspondences and pure generators as
`parameterTensorPresheaf` and imposes no geometric condition on a parameter.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory TensorProduct

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]
variable (F : Cor k ⥤ Cor k) [F.Additive]

/-- Restrict a transfer presheaf along an additive correspondence functor. -/
def additivePrecompose :
    PresheafWithTransfers.{u + 1} k ⥤ PresheafWithTransfers.{u + 1} k where
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
def coendPushforwardUnit (P : PresheafWithTransfers.{u + 1} k) :
    P ⟶ (additivePrecompose F).obj (parameterTensorPresheaf F P) :=
  ObjectProperty.homMk
    { app X := by
        let W := (F).obj X.unop
        let j : ModuleCat.of ℤ (sections P X.unop ⊗[ℤ] ULift.{u + 1} (W ⟶ W)) ⟶
            parameterTensorSections F P W := coend.ι (parameterTensorDiagram F P W) X.unop
        let a : ULift.{u + 1} (W ⟶ W) := ULift.up (𝟙 W)
        change sections P X.unop ⟶ AddCommGrpCat.of (parameterTensorSections F P W)
        exact AddCommGrpCat.ofHom
          { toFun := fun s => parameterTensorGenerator F P W X.unop s (𝟙 _)
            map_zero' := by
              change j ((0 : sections P X.unop) ⊗ₜ[ℤ] a) = 0
              rw [TensorProduct.zero_tmul, map_zero]
            map_add' := by
              intro s t
              change j ((s + t) ⊗ₜ[ℤ] a) = j (s ⊗ₜ[ℤ] a) + j (t ⊗ₜ[ℤ] a)
              rw [TensorProduct.add_tmul, map_add] }
      naturality X Y β := by
        apply AddCommGrpCat.ext
        intro s
        change parameterTensorGenerator F P ((F).obj Y.unop) Y.unop (transfer P β.unop s) (𝟙 _) =
          parameterTensorTransfer F P ((F).map β.unop)
            (parameterTensorGenerator F P ((F).obj X.unop) X.unop s (𝟙 _))
        rw [parameterTensorTransfer_generator, Category.comp_id, parameterTensorGenerator_transfer,
          Category.id_comp] }

theorem coendPushforwardUnit_app_apply (P : PresheafWithTransfers.{u + 1} k)
    (X : Cor k) (s : sections P X) :
    (coendPushforwardUnit F P).hom.app (op X) s =
      parameterTensorGenerator F P ((F).obj X) X s (𝟙 _) := rfl


variable {P Q : PresheafWithTransfers.{u + 1} k}

/-- Evaluate the actual signed transfer against the value of a coefficient map. -/
def coendPushforwardPairing (θ : P ⟶ (additivePrecompose F).obj Q) (X Y : Cor k) :
    ((parameterTensorDiagram F P X).obj (op Y)).obj Y ⟶
      ModuleCat.of ℤ (sections Q X) := by
  let h : sections P Y ⟶ sections Q ((F).obj Y) := θ.hom.app (op Y)
  let ev (s : sections P Y) : ULift.{u + 1} (X ⟶ (F).obj Y) →+ sections Q X :=
    { toFun := fun a => transfer Q a.down (h s)
      map_zero' := by rw [show (0 : ULift.{u + 1} (X ⟶ (F).obj Y)).down = 0 from rfl,
        transfer_zero]; rfl
      map_add' a b := by
        change transfer Q (a.down + b.down) _ = _
        rw [transfer_add]
        rfl }
  let e : sections P Y →+ (ULift.{u + 1} (X ⟶ (F).obj Y) →ₗ[ℤ] sections Q X) :=
    { toFun := fun s => (ev s).toIntLinearMap
      map_zero' := by
        ext a
        change transfer Q a.down (h 0) = 0
        rw [map_zero, map_zero]
      map_add' s t := by
        ext a
        change transfer Q a.down (h (s + t)) =
          transfer Q a.down (h s) + transfer Q a.down (h t)
        rw [map_add, map_add] }
  exact ModuleCat.ofHom (TensorProduct.lift e.toIntLinearMap)

@[simp]
theorem coendPushforwardPairing_tmul (θ : P ⟶ (additivePrecompose F).obj Q) (X Y : Cor k)
    (s : sections P Y) (a : ULift.{u + 1} (X ⟶ (F).obj Y)) :
    coendPushforwardPairing F θ X Y (s ⊗ₜ[ℤ] a) = transfer Q a.down (θ.hom.app (op Y) s) := rfl

/-- The transfer pairing identifies the two maps in the coend relation. -/
theorem coendPushforwardPairing_dinatural (θ : P ⟶ (additivePrecompose F).obj Q)
    (X : Cor k) {Y Z : Cor k} (f : Y ⟶ Z) :
    ((parameterTensorDiagram F P X).map f.op).app Y ≫ coendPushforwardPairing F θ X Y =
      ((parameterTensorDiagram F P X).obj (op Z)).map f ≫ coendPushforwardPairing F θ X Z := by
  let A := P.obj ⋙ integerModuleFunctor
  let B := parameterCorrespondenceModule F X
  change (A.map f.op ⊗ₘ B.map (𝟙 Y)) ≫ coendPushforwardPairing F θ X Y =
    (A.map (𝟙 (op Z)) ⊗ₘ B.map f) ≫ coendPushforwardPairing F θ X Z
  rw [A.map_id, B.map_id]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro s a
  change ULift.{u + 1} (X ⟶ (F).obj Y) at a
  have h := ConcreteCategory.congr_hom (transfer_naturality θ f) s
  change θ.hom.app (op Y) (transfer P f s) =
    transfer Q ((F).map f) (θ.hom.app (op Z) s) at h
  change transfer Q a.down (θ.hom.app (op Y) (transfer P f s)) =
    transfer Q (a.down ≫ (F).map f) (θ.hom.app (op Z) s)
  rw [h, transfer_comp]
  rfl

/-- The native coend map induced by the transfer pairing. -/
def coendPushforwardDescApp (θ : P ⟶ (additivePrecompose F).obj Q) (X : Cor k) :
    parameterTensorSections F P X ⟶ ModuleCat.of ℤ (sections Q X) :=
  coend.desc («F» := parameterTensorDiagram F P X) (coendPushforwardPairing F θ X)
    (fun _ _ f => coendPushforwardPairing_dinatural F θ X f)

/-- On every generator the coend map is the actual signed transfer. -/
@[simp]
theorem coendPushforwardDescApp_generator (θ : P ⟶ (additivePrecompose F).obj Q) (X Y : Cor k)
    (s : sections P Y) (a : X ⟶ (F).obj Y) :
    coendPushforwardDescApp F θ X (parameterTensorGenerator F P X Y s a) =
      transfer Q a (θ.hom.app (op Y) s) := by
  change (coend.ι (parameterTensorDiagram F P X) Y ≫
    coendPushforwardDescApp F θ X) (s ⊗ₜ[ℤ] ULift.up a) = _
  rw [coendPushforwardDescApp, coend.ι_desc]
  exact coendPushforwardPairing_tmul F θ X Y s (ULift.up a)

/-- Evaluation from the coend commutes with every actual source correspondence. -/
@[reassoc]
theorem coendPushforwardDescApp_naturality (θ : P ⟶ (additivePrecompose F).obj Q)
    {X X' : Cor k} (β : X' ⟶ X) :
    parameterTensorTransfer F P β ≫ coendPushforwardDescApp F θ X' =
      coendPushforwardDescApp F θ X ≫ integerModuleFunctor.map (transfer Q β) := by
  apply parameterTensorSections_hom_ext
  intro Y s a
  change coendPushforwardDescApp F θ X' (parameterTensorTransfer F P β
    (parameterTensorGenerator F P X Y s a)) =
      transfer Q β (coendPushforwardDescApp F θ X (parameterTensorGenerator F P X Y s a))
  rw [parameterTensorTransfer_generator, coendPushforwardDescApp_generator,
    coendPushforwardDescApp_generator, transfer_comp]
  rfl

/-- Descend the original coefficient pairing as a morphism with transfers. -/
def coendPushforwardDesc (θ : P ⟶ (additivePrecompose F).obj Q) : parameterTensorPresheaf F P ⟶ Q :=
  ObjectProperty.homMk
    { app X := (forget₂ (ModuleCat ℤ) AddCommGrpCat).map (coendPushforwardDescApp F θ X.unop)
      naturality X Y β := by
        let U := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
        change U.map (parameterTensorTransfer F P β.unop) ≫
          U.map (coendPushforwardDescApp F θ Y.unop) =
          U.map (coendPushforwardDescApp F θ X.unop) ≫
            U.map (integerModuleFunctor.map (transfer Q β.unop))
        exact (U.map_comp _ _).symm.trans
          ((congrArg (fun f => U.map f) (coendPushforwardDescApp_naturality F θ β.unop)).trans
            (U.map_comp _ _)) }

@[simp]
theorem coendPushforwardDesc_app_generator (θ : P ⟶ (additivePrecompose F).obj Q) (X Y : Cor k)
    (s : sections P Y) (a : X ⟶ (F).obj Y) :
    (coendPushforwardDesc F θ).hom.app (op X) (parameterTensorGenerator F P X Y s a) =
      transfer Q a (θ.hom.app (op Y) s) :=
  coendPushforwardDescApp_generator F θ X Y s a


/-- The adjunction bijection, with the specified transfer and unit formulas. -/
def coendPushforwardHomEquiv (P Q : (PresheafWithTransfers.{u + 1} k)) :
    (parameterTensorPresheaf F P ⟶ Q) ≃ (P ⟶ (additivePrecompose F).obj Q) where
  toFun f := coendPushforwardUnit F P ≫ (additivePrecompose F).map f
  invFun := coendPushforwardDesc F
  left_inv f := by
    apply parameterTensorPresheaf_hom_ext
    intro X Y s a
    rw [coendPushforwardDesc_app_generator]
    let z := parameterTensorGenerator F P ((F).obj Y) Y s (𝟙 _)
    change transfer Q a (f.hom.app (op ((F).obj Y)) z) =
      f.hom.app (op X) (parameterTensorGenerator F P X Y s a)
    have h := ConcreteCategory.congr_hom (transfer_naturality f a) z
    change f.hom.app (op X) (parameterTensorTransfer F P a z) =
      transfer Q a (f.hom.app (op ((F).obj Y)) z) at h
    rw [show z = parameterTensorGenerator F P ((F).obj Y) Y s (𝟙 _) from rfl,
      parameterTensorTransfer_generator, Category.comp_id] at h
    exact h.symm
  right_inv θ := by
    apply ObjectProperty.hom_ext
    ext X s
    change (coendPushforwardDesc F θ).hom.app (op ((F).obj X.unop))
      (parameterTensorGenerator F P ((F).obj X.unop) X.unop s (𝟙 _)) = θ.hom.app X s
    rw [coendPushforwardDesc_app_generator, transfer_id]
    rfl

/-- The parameter adjunction acts by the original coefficient maps on the right. -/
theorem coendPushforwardHomEquiv_naturality_right (P Q Q' : PresheafWithTransfers.{u + 1} k)
    (g : Q ⟶ Q') (f : parameterTensorPresheaf F P ⟶ Q) :
    coendPushforwardHomEquiv F P Q' (f ≫ g) =
      coendPushforwardHomEquiv F P Q f ≫
        (additivePrecompose F :
          PresheafWithTransfers.{u + 1} k ⥤ PresheafWithTransfers.{u + 1} k).map g := by
  let R : PresheafWithTransfers.{u + 1} k ⥤ PresheafWithTransfers.{u + 1} k :=
    additivePrecompose F
  let η : P ⟶ R.obj (parameterTensorPresheaf F P) := coendPushforwardUnit F P
  change η ≫ R.map (f ≫ g) = (η ≫ R.map f) ≫ R.map g
  exact (congrArg (fun h => η ≫ h) (R.map_comp f g)).trans
    (Category.assoc η (R.map f) (R.map g)).symm

/-- Tensoring with the parameter is left adjoint to its original section functor. -/
def coendPushforward : PresheafWithTransfers.{u + 1} k ⥤ PresheafWithTransfers.{u + 1} k :=
  Adjunction.leftAdjointOfEquiv
    (G := (additivePrecompose F :
      PresheafWithTransfers.{u + 1} k ⥤ PresheafWithTransfers.{u + 1} k))
    (F_obj := parameterTensorPresheaf F) (coendPushforwardHomEquiv F)
    (coendPushforwardHomEquiv_naturality_right F)

/-- The adjunction on the original transfer categories. -/
def coendPushforwardAdjunction :
    coendPushforward F ⊣ (additivePrecompose F :
      PresheafWithTransfers.{u + 1} k ⥤ PresheafWithTransfers.{u + 1} k) :=
  Adjunction.adjunctionOfEquivLeft
    (G := (additivePrecompose F :
      PresheafWithTransfers.{u + 1} k ⥤ PresheafWithTransfers.{u + 1} k))
    (F_obj := parameterTensorPresheaf F) (coendPushforwardHomEquiv F)
    (coendPushforwardHomEquiv_naturality_right F)

instance : (coendPushforward F).IsLeftAdjoint :=
  (coendPushforwardAdjunction F).isLeftAdjoint

instance : (coendPushforward F).Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts (coendPushforward F)
  exact Functor.additive_of_preservesBinaryBiproducts (coendPushforward F)

/-- The actual adjunction unit is the original pure-tensor map. -/
@[simp]
theorem coendPushforwardAdjunction_unit_app (P : PresheafWithTransfers.{u + 1} k) :
    (coendPushforwardAdjunction F).unit.app P = coendPushforwardUnit F P := by
  let R : PresheafWithTransfers.{u + 1} k ⥤ PresheafWithTransfers.{u + 1} k :=
    additivePrecompose F
  let η : P ⟶ R.obj (parameterTensorPresheaf F P) := coendPushforwardUnit F P
  change η ≫ R.map (𝟙 (parameterTensorPresheaf F P)) = η
  rw [R.map_id, Category.comp_id]


end AlgebraicGeometry.PresheafWithTransfers
