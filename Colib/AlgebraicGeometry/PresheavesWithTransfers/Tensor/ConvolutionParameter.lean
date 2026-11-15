/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ConvolutionFunctor
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.PushforwardExactness
import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.Representable
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.RepresentableLarge

/-!
# Convolution with a represented parameter

The two-variable integral coend with a representable in its second slot
is the pushforward along the original right parameter functor. The comparison
uses the literal identity correspondence in the represented slot of the unit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory TensorProduct

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]
variable (F : Cor k ⥤ Cor k ⥤ Cor k) [F.Additive] [∀ Y, (F.obj Y).Additive]
variable (T : Cor k)

local instance : (F.flip.obj T).Additive where
  map_add := by
    intro X Y f g
    change (F.map (f + g)).app T = (F.map f).app T + (F.map g).app T
    exact NatTrans.congr_app (F.map_add (f := f) (g := g)) T

/-- Postcomposition with the image of the parameter correspondence, extended linearly over `ℤ`. -/
def convolutionParameterComposition (U Y Z : Cor k) :
    (ULift.{u + 1} (Z ⟶ T) ⊗[ℤ] ULift.{u + 1} (U ⟶ (F.obj Y).obj Z)) →ₗ[ℤ]
      ULift.{u + 1} (U ⟶ (F.obj Y).obj T) := by
  let e (b : ULift.{u + 1} (Z ⟶ T)) :
      ULift.{u + 1} (U ⟶ (F.obj Y).obj Z) →+ ULift.{u + 1} (U ⟶ (F.obj Y).obj T) :=
    AddMonoidHom.mk' (fun a => ULift.up (a.down ≫ (F.obj Y).map b.down)) (by
      intro a a'
      apply congrArg ULift.up
      exact Preadditive.add_comp _ _ _ _ _ _)
  let f : ULift.{u + 1} (Z ⟶ T) →+
      (ULift.{u + 1} (U ⟶ (F.obj Y).obj Z) →ₗ[ℤ] ULift.{u + 1} (U ⟶ (F.obj Y).obj T)) :=
    AddMonoidHom.mk' (fun b => (e b).toIntLinearMap) (by
      intro b b'
      apply LinearMap.ext
      intro a
      apply ULift.ext
      change a.down ≫ (F.obj Y).map (b.down + b'.down) =
        a.down ≫ (F.obj Y).map b.down + a.down ≫ (F.obj Y).map b'.down
      rw [Functor.map_add, Preadditive.comp_add])
  let g : ULift.{u + 1} (Z ⟶ T) →ₗ[ℤ]
      (ULift.{u + 1} (U ⟶ (F.obj Y).obj Z) →ₗ[ℤ] ULift.{u + 1} (U ⟶ (F.obj Y).obj T)) :=
    { toFun := f
      map_add' := f.map_add
      map_smul' n b := (f.map_zsmul n b).trans (int_smul_eq_zsmul inferInstance n (f b)).symm }
  exact TensorProduct.lift g

/-- Send a convolution generator to the parameter coend by composing its two correspondences. -/
def convolutionParameterPairing (P : PresheafWithTransfers.{u + 1} k) (U Y Z : Cor k) :
    ModuleCat.of ℤ ((sections P Y ⊗[ℤ] ULift.{u + 1} (Z ⟶ T)) ⊗[ℤ]
      ULift.{u + 1} (U ⟶ (F.obj Y).obj Z)) ⟶ parameterTensorSections (F.flip.obj T) P U :=
  let j : ModuleCat.of ℤ (sections P Y ⊗[ℤ] ULift.{u + 1} (U ⟶ (F.obj Y).obj T)) ⟶
      parameterTensorSections (F.flip.obj T) P U :=
    coend.ι (parameterTensorDiagram (F.flip.obj T) P U) Y
  ModuleCat.ofHom ((TensorProduct.map LinearMap.id (convolutionParameterComposition F T U Y Z)).comp
    (TensorProduct.assoc ℤ (sections P Y) (ULift.{u + 1} (Z ⟶ T))
      (ULift.{u + 1} (U ⟶ (F.obj Y).obj Z))).toLinearMap) ≫ j

/-- The pairing from a diagonal term of the convolution diagram to the parameter coend. -/
def convolutionParameterDiagramPairing (P : PresheafWithTransfers.{u + 1} k)
    (U : Cor k) (YZ : Cor k × Cor k) :
    ((convolutionDiagram F P ((representableLarge k).obj T) U).obj (op YZ)).obj YZ ⟶
      parameterTensorSections (F.flip.obj T) P U :=
  convolutionParameterPairing F T P U YZ.1 YZ.2

set_option maxHeartbeats 1000000 in
-- The three bundled coefficient modules must be reduced to expose their pure tensors.
omit [F.Additive] in
theorem convolutionParameterPairing_dinatural (P : PresheafWithTransfers.{u + 1} k)
    (U : Cor k) {YZ Y'Z' : Cor k × Cor k} (fg : YZ ⟶ Y'Z') :
    let D := convolutionDiagram F P ((representableLarge k).obj T) U
    (D.map fg.op).app YZ ≫ convolutionParameterDiagramPairing F T P U YZ =
      (D.obj (op Y'Z')).map fg ≫ convolutionParameterDiagramPairing F T P U Y'Z' := by
  obtain ⟨Y, Z⟩ := YZ
  obtain ⟨Y', Z'⟩ := Y'Z'
  let f := fg.1
  let g := fg.2
  let A := convolutionCoefficientModule P ((representableLarge k).obj T)
  let B := convolutionCorrespondenceModule F U
  let C := ModuleCat.of ℤ ((sections P Y' ⊗[ℤ] ULift.{u + 1} (Z' ⟶ T)) ⊗[ℤ]
    ULift.{u + 1} (U ⟶ (F.obj Y).obj Z))
  let H := parameterTensorSections (F.flip.obj T) P U
  let l : C ⟶ H := (A.map fg.op ⊗ₘ B.map (𝟙 (Y, Z))) ≫
    convolutionParameterPairing F T P U Y Z
  let r : C ⟶ H := (A.map (𝟙 (op (Y', Z'))) ⊗ₘ B.map fg) ≫
    convolutionParameterPairing F T P U Y' Z'
  change l = r
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  rintro sb ⟨a⟩
  refine TensorProduct.inductionOn sb ?_ ?_
  · rintro s ⟨b⟩
    change l ((s ⊗ₜ[ℤ] ULift.up b) ⊗ₜ[ℤ] ULift.up a) =
      r ((s ⊗ₜ[ℤ] ULift.up b) ⊗ₜ[ℤ] ULift.up a)
    dsimp only [l, r]
    rw [A.map_id, B.map_id]
    change parameterTensorGenerator (F.flip.obj T) P U Y (transfer P f s)
        (a ≫ (F.obj Y).map (g ≫ b)) =
      parameterTensorGenerator (F.flip.obj T) P U Y' s
        ((a ≫ convolutionCorrespondenceMap F f g) ≫ (F.obj Y').map b)
    have ht := parameterTensorGenerator_transfer (F.flip.obj T) P f s
      (a ≫ (F.obj Y).map (g ≫ b))
    refine ht.trans (congrArg (parameterTensorGenerator (F.flip.obj T) P U Y' s) ?_)
    change (a ≫ (F.obj Y).map (g ≫ b)) ≫ (F.map f).app T =
      (a ≫ ((F.map f).app Z ≫ (F.obj Y').map g)) ≫ (F.obj Y').map b
    rw [(F.obj Y).map_comp, Category.assoc, Category.assoc, Category.assoc,
      (F.map f).naturality b, (F.map f).naturality_assoc g]
    simp only [Category.assoc]
  · intro s t hs ht
    let a₁ : C := s ⊗ₜ[ℤ] ULift.up a
    let a₂ : C := t ⊗ₜ[ℤ] ULift.up a
    have h : (s + t) ⊗ₜ[ℤ] ULift.up a = (a₁ + a₂ : C) := TensorProduct.add_tmul _ _ _
    calc
      l.hom ((s + t) ⊗ₜ[ℤ] ULift.up a) = l.hom (a₁ + a₂) := congrArg _ h
      _ = l.hom a₁ + l.hom a₂ := l.hom.map_add _ _
      _ = r.hom a₁ + r.hom a₂ := congrArg₂ (· + ·) hs ht
      _ = r.hom (a₁ + a₂) := (r.hom.map_add _ _).symm
      _ = r.hom ((s + t) ⊗ₜ[ℤ] ULift.up a) := congrArg _ h.symm

/-- The map on sections induced by the dinatural pairing for a represented right parameter. -/
def convolutionParameterHomApp (P : PresheafWithTransfers.{u + 1} k) (U : Cor k) :
    convolutionSections F P ((representableLarge k).obj T) U ⟶
      parameterTensorSections (F.flip.obj T) P U :=
  coend.desc («F» := convolutionDiagram F P ((representableLarge k).obj T) U)
    (convolutionParameterDiagramPairing F T P U)
    (fun _ _ fg => convolutionParameterPairing_dinatural F T P U fg)

omit [F.Additive] in
@[simp]
private theorem convolutionParameterHomApp_generator (P : PresheafWithTransfers.{u + 1} k)
    (U Y Z : Cor k) (s : sections P Y) (b : Z ⟶ T) (a : U ⟶ (F.obj Y).obj Z) :
    convolutionParameterHomApp F T P U
      (convolutionGenerator F P ((representableLarge k).obj T) U Y Z s (ULift.up b) a) =
      parameterTensorGenerator (F.flip.obj T) P U Y s (a ≫ (F.obj Y).map b) := by
  change (coend.ι (convolutionDiagram F P ((representableLarge k).obj T) U) (Y, Z) ≫
    convolutionParameterHomApp F T P U) ((s ⊗ₜ[ℤ] ULift.up b) ⊗ₜ[ℤ] ULift.up a) = _
  have h := coend.ι_desc
    (convolutionParameterDiagramPairing F T P U)
    (fun _ _ fg => convolutionParameterPairing_dinatural F T P U fg)
    (Y, Z)
  exact ConcreteCategory.congr_hom h _

/-- The comparison from convolution with a right representable to additive coend pushforward. -/
def convolutionParameterHom (P : PresheafWithTransfers.{u + 1} k) :
    convolutionPresheaf F P ((representableLarge k).obj T) ⟶
      (coendPushforward (F.flip.obj T)).obj P :=
  ObjectProperty.homMk
    { app U := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).map
        (convolutionParameterHomApp F T P U.unop)
      naturality U U' β := by
        let V := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
        change V.map (convolutionTransfer F P ((representableLarge k).obj T) β.unop) ≫
            V.map (convolutionParameterHomApp F T P U'.unop) =
          V.map (convolutionParameterHomApp F T P U.unop) ≫
            V.map (parameterTensorTransfer (F.flip.obj T) P β.unop)
        rw [← V.map_comp, ← V.map_comp]
        apply congrArg V.map
        apply convolutionSections_hom_ext
        intro Y Z s b a
        change ULift.{u + 1} (Z ⟶ T) at b
        obtain ⟨b⟩ := b
        let q := (representableLarge k).obj T
        let t : sections q Z := ULift.up b
        let z := convolutionGenerator F P q U.unop Y Z s t a
        let m := convolutionParameterHomApp F T P U'.unop
        let n := parameterTensorTransfer (F.flip.obj T) P β.unop
        change m (convolutionTransfer F P q β.unop z) =
          n (convolutionParameterHomApp F T P U.unop z)
        have h₁ := convolutionTransfer_generator F P q β.unop Y Z s t a
        have h₂ := convolutionParameterHomApp_generator F T P U'.unop Y Z s b (β.unop ≫ a)
        have h₃ := convolutionParameterHomApp_generator F T P U.unop Y Z s b a
        have h₄ := parameterTensorTransfer_generator (F.flip.obj T) P β.unop Y s
          (a ≫ (F.obj Y).map b)
        have h₅ := congrArg (parameterTensorGenerator (F.flip.obj T) P U'.unop Y s)
          (Category.assoc β.unop a ((F.obj Y).map b))
        exact (congrArg m h₁).trans (h₂.trans
          (h₅.trans (h₄.symm.trans (congrArg n h₃).symm))) }

/-- The unit sends a section to the coend generator of the two identity correspondences. -/
def convolutionParameterUnit (P : PresheafWithTransfers.{u + 1} k) :
    P ⟶ (additivePrecompose (F.flip.obj T)).obj
      (convolutionPresheaf F P ((representableLarge k).obj T)) :=
  ObjectProperty.homMk
    { app Y := by
        let U := (F.obj Y.unop).obj T
        let j := convolutionInclusion F P ((representableLarge k).obj T) U Y.unop T
        let b : sections ((representableLarge k).obj T) T := ULift.up (𝟙 T)
        let a : ULift.{u + 1} (U ⟶ U) := ULift.up (𝟙 U)
        exact AddCommGrpCat.ofHom
          { toFun := fun s => convolutionGenerator F P ((representableLarge k).obj T)
              U Y.unop T s b (𝟙 U)
            map_zero' := by
              change j (((0 : sections P Y.unop) ⊗ₜ[ℤ] b) ⊗ₜ[ℤ] a) = 0
              rw [TensorProduct.zero_tmul, TensorProduct.zero_tmul, map_zero]
            map_add' := fun s s' =>
              convolutionGenerator_add_left F P ((representableLarge k).obj T) s s' b (𝟙 U) }
      naturality Y Y' β := by
        apply AddCommGrpCat.ext
        intro s
        change convolutionGenerator F P ((representableLarge k).obj T)
            ((F.obj Y'.unop).obj T) Y'.unop T (transfer P β.unop s) (ULift.up (𝟙 T)) (𝟙 _) =
          convolutionTransfer F P ((representableLarge k).obj T) ((F.map β.unop).app T)
            (convolutionGenerator F P ((representableLarge k).obj T)
              ((F.obj Y.unop).obj T) Y.unop T s (ULift.up (𝟙 T)) (𝟙 _))
        let q := (representableLarge k).obj T
        let t : sections q T := ULift.up (𝟙 T)
        let a := (F.map β.unop).app T
        have h := convolutionGenerator_transfer F P q β.unop (𝟙 T) s t
          (𝟙 ((F.obj Y'.unop).obj T))
        have h₁ : transfer q (𝟙 T) t = t := ConcreteCategory.congr_hom (transfer_id q T) t
        have h₂ : 𝟙 ((F.obj Y'.unop).obj T) ≫ convolutionCorrespondenceMap F β.unop (𝟙 T) = a :=
          (Category.id_comp _).trans
            ((congrArg (a ≫ ·) ((F.obj Y.unop).map_id T)).trans (Category.comp_id a))
        have h₃ := convolutionTransfer_generator F P q a Y.unop T s t (𝟙 _)
        have h₄ := congrArg (convolutionGenerator F P q ((F.obj Y'.unop).obj T) Y.unop T s t)
          (Category.comp_id a)
        exact (congrArg (fun t₀ =>
          convolutionGenerator F P q ((F.obj Y'.unop).obj T) Y'.unop T
            (transfer P β.unop s) t₀ (𝟙 _)) h₁).symm.trans
          (h.trans ((congrArg (convolutionGenerator F P q ((F.obj Y'.unop).obj T) Y.unop T s t)
            h₂).trans (h₄.symm.trans h₃.symm))) }

/-- The reverse comparison induced by the coend unit with identity correspondences. -/
def convolutionParameterInv (P : PresheafWithTransfers.{u + 1} k) :
    (coendPushforward (F.flip.obj T)).obj P ⟶
      convolutionPresheaf F P ((representableLarge k).obj T) :=
  coendPushforwardDesc (F.flip.obj T) (convolutionParameterUnit F T P)

omit [∀ Y, (F.obj Y).Additive] in
@[simp]
private theorem convolutionParameterInv_generator (P : PresheafWithTransfers.{u + 1} k)
    (U Y : Cor k) (s : sections P Y) (a : U ⟶ (F.obj Y).obj T) :
    (convolutionParameterInv F T P).hom.app (op U)
      (parameterTensorGenerator (F.flip.obj T) P U Y s a) =
    convolutionGenerator F P ((representableLarge k).obj T) U Y T s (ULift.up (𝟙 T)) a := by
  let q := (representableLarge k).obj T
  let t : sections q T := ULift.up (𝟙 T)
  let G := F.flip.obj T
  have h := coendPushforwardDesc_app_generator G (convolutionParameterUnit F T P) U Y s a
  change (convolutionParameterInv F T P).hom.app (op U)
      (parameterTensorGenerator G P U Y s a) =
    convolutionTransfer F P q a
      (convolutionGenerator F P q (G.obj Y) Y T s t (𝟙 _)) at h
  exact h.trans ((convolutionTransfer_generator F P q a Y T s t (𝟙 _)).trans
    (congrArg (convolutionGenerator F P q U Y T s t) (Category.comp_id a)))

/-- Tensoring with a represented right parameter agrees with the original coend pushforward. -/
def convolutionParameterIso (P : PresheafWithTransfers.{u + 1} k) :
    convolutionPresheaf F P ((representableLarge k).obj T) ≅
      (coendPushforward (F.flip.obj T)).obj P where
  hom := convolutionParameterHom F T P
  inv := convolutionParameterInv F T P
  hom_inv_id := by
    apply convolutionPresheaf_hom_ext
    intro U Y Z s b a
    change ULift.{u + 1} (Z ⟶ T) at b
    obtain ⟨b⟩ := b
    let q := (representableLarge k).obj T
    let t : sections q Z := ULift.up b
    let t₀ : sections q T := ULift.up (𝟙 T)
    let z := convolutionGenerator F P q U Y Z s t a
    let m := (convolutionParameterInv F T P).hom.app (op U)
    let a' := a ≫ (F.obj Y).map b
    change m (convolutionParameterHomApp F T P U z) = z
    have h₁ := convolutionParameterHomApp_generator F T P U Y Z s b a
    have h₂ := convolutionParameterInv_generator F T P U Y s a'
    have ht : transfer q b t₀ = t := by
      change ULift.up (b ≫ 𝟙 T) = ULift.up b
      exact congrArg ULift.up (Category.comp_id b)
    have hs : transfer P (𝟙 Y) s = s := ConcreteCategory.congr_hom (transfer_id P Y) s
    have h := convolutionGenerator_transfer F P q (𝟙 Y) b s t₀ a
    have h' : a ≫ convolutionCorrespondenceMap F (𝟙 Y) b = a' := by
      change a ≫ (F.map (𝟙 Y)).app Z ≫ (F.obj Y).map b = _
      rw [show (F.map (𝟙 Y)).app Z = 𝟙 _ from NatTrans.congr_app (F.map_id Y) Z,
        Category.id_comp]
    have h₃ : z = convolutionGenerator F P q U Y T s t₀ a' :=
      ((congrArg₂ (fun s₀ t₁ => convolutionGenerator F P q U Y Z s₀ t₁ a) hs ht).symm.trans h).trans
        (congrArg (convolutionGenerator F P q U Y T s t₀) h')
    exact (congrArg m h₁).trans (h₂.trans h₃.symm)
  inv_hom_id := by
    apply parameterTensorPresheaf_hom_ext
    intro U Y s a
    let G := F.flip.obj T
    let z := parameterTensorGenerator G P U Y s a
    let m := convolutionParameterHomApp F T P U
    change m ((convolutionParameterInv F T P).hom.app (op U) z) = z
    have h₁ := convolutionParameterInv_generator F T P U Y s a
    have h₂ := convolutionParameterHomApp_generator F T P U Y T s (𝟙 T) a
    have h₃ : a ≫ (F.obj Y).map (𝟙 T) = a :=
      (congrArg (a ≫ ·) ((F.obj Y).map_id T)).trans (Category.comp_id a)
    exact (congrArg m h₁).trans (h₂.trans (congrArg (parameterTensorGenerator G P U Y s) h₃))

@[simp]
theorem convolutionParameterIso_hom_generator (P : PresheafWithTransfers.{u + 1} k)
    (U Y Z : Cor k) (s : sections P Y) (b : Z ⟶ T) (a : U ⟶ (F.obj Y).obj Z) :
    (convolutionParameterIso F T P).hom.hom.app (op U)
      (convolutionGenerator F P ((representableLarge k).obj T) U Y Z s (ULift.up b) a) =
      parameterTensorGenerator (F.flip.obj T) P U Y s (a ≫ (F.obj Y).map b) :=
  convolutionParameterHomApp_generator F T P U Y Z s b a

/-- The comparison identifies the unit on each literal generator with the pushforward unit. -/
theorem convolutionParameterIso_unit (P : PresheafWithTransfers.{u + 1} k) :
    convolutionParameterUnit F T P ≫
        (additivePrecompose (F.flip.obj T)).map (convolutionParameterIso F T P).hom =
      coendPushforwardUnit (F.flip.obj T) P := by
  apply ObjectProperty.hom_ext
  ext Y s
  change (convolutionParameterIso F T P).hom.hom.app (op ((F.obj Y.unop).obj T))
    (convolutionGenerator F P ((representableLarge k).obj T) ((F.obj Y.unop).obj T)
      Y.unop T s (ULift.up (𝟙 T)) (𝟙 _)) = _
  have h := convolutionParameterIso_hom_generator F T P
    ((F.obj Y.unop).obj T) Y.unop T s (𝟙 T) (𝟙 _)
  have h' : 𝟙 ((F.obj Y.unop).obj T) ≫ (F.obj Y.unop).map (𝟙 T) = 𝟙 _ :=
    (Category.id_comp _).trans ((F.obj Y.unop).map_id T)
  exact h.trans (congrArg
    (parameterTensorGenerator (F.flip.obj T) P ((F.obj Y.unop).obj T) Y.unop s) h')

omit [∀ Y, (F.obj Y).Additive] in
/-- Convolution with the right represented parameter is naturally the coend pushforward. -/
def convolutionParameterNatIso :
    (convolutionBifunctor F).flip.obj ((representableLarge k).obj T) ≅
      coendPushforward (F.flip.obj T) :=
  NatIso.ofComponents (convolutionParameterIso F T) (fun {P Q} f => by
    apply convolutionPresheaf_hom_ext
    intro U Y Z s b a
    change ULift.{u + 1} (Z ⟶ T) at b
    obtain ⟨b⟩ := b
    change (convolutionParameterIso F T Q).hom.hom.app (op U)
        ((convolutionMap F f (𝟙 ((representableLarge k).obj T))).hom.app (op U)
          (convolutionGenerator F P ((representableLarge k).obj T) U Y Z s (ULift.up b) a)) =
      ((coendPushforward (F.flip.obj T)).map f).hom.app (op U)
        ((convolutionParameterIso F T P).hom.hom.app (op U)
          (convolutionGenerator F P ((representableLarge k).obj T) U Y Z s (ULift.up b) a))
    let q := (representableLarge k).obj T
    let t : sections q Z := ULift.up b
    let z := convolutionGenerator F P q U Y Z s t a
    let m := (convolutionParameterIso F T Q).hom.hom.app (op U)
    let n := ((coendPushforward (F.flip.obj T)).map f).hom.app (op U)
    let w := (convolutionParameterIso F T P).hom.hom.app (op U)
    have ht : (𝟙 q : q ⟶ q).hom.app (op Z) t = t := rfl
    have h₁ := convolutionMap_generator F f (𝟙 q) U Y Z s t a
    have h₂ := congrArg (fun t₀ => convolutionGenerator F Q q U Y Z
      (f.hom.app (op Y) s) t₀ a) ht
    have h₃ := convolutionParameterIso_hom_generator F T Q U Y Z (f.hom.app (op Y) s) b a
    have h₄ := convolutionParameterIso_hom_generator F T P U Y Z s b a
    have h₅ := coendPushforward_map_generator (F.flip.obj T) f U Y s (a ≫ (F.obj Y).map b)
    change m ((convolutionMap F f (𝟙 q)).hom.app (op U) z) = n (w z)
    exact (congrArg m (h₁.trans h₂)).trans (h₃.trans (h₅.symm.trans (congrArg n h₄).symm)))

end AlgebraicGeometry.PresheafWithTransfers
