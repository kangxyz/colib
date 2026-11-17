/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Preadditive.IntegralConvolutionFunctor
public import Colib.CategoryTheory.Preadditive.ParameterCoendUnit
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# Convolution with a represented parameter

The two-variable integral coend with a representable in its second slot
is the pushforward along the original right parameter functor. The comparison
uses the literal identity correspondence in the represented slot of the unit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory TensorProduct

universe u v w

namespace CategoryTheory.Preadditive.ConvolutionRepresented

variable {C : Type u} [Category.{v} C] [Preadditive C]
open CategoryTheory.Preadditive.ParameterCoend

/-- Universe lifting preserves addition of morphisms of abelian groups. -/
instance uliftAdditive : AddCommGrpCat.uliftFunctor.{w, v}.Additive where
  map_add := by intros; ext x; rfl

/-- The lifted additive representable, with the actual additive Hom groups. -/
def represented (T : C) : Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w} :=
  AdditiveFunctor.of (preadditiveYoneda.obj T ⋙ AddCommGrpCat.uliftFunctor.{max u v w, v})

/-- A pure integral coend generator for bundled additive coefficients. -/
abbrev convolutionGenerator (F : C ⥤ C ⥤ C) (P Q : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u
    v w})) :=
  Convolution.generator.{u, v, w} F P.obj Q.obj

/-- The integral coend inclusion for bundled additive coefficients. -/
abbrev convolutionInclusion (F : C ⥤ C ⥤ C) (P Q : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u
    v w})) :=
  Convolution.inclusion.{u, v, w} F P.obj Q.obj

/-- The integral coend diagram for bundled additive coefficients. -/
abbrev convolutionDiagram (F : C ⥤ C ⥤ C) (P Q : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v
    w})) :=
  Convolution.diagram.{u, v, w} F P.obj Q.obj

/-- The integral coend sections for bundled additive coefficients. -/
abbrev convolutionSections (F : C ⥤ C ⥤ C) (P Q : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u
    v w})) :=
  Convolution.sections.{u, v, w} F P.obj Q.obj

/-- The source action on the integral coend for bundled additive coefficients. -/
abbrev convolutionTransfer (F : C ⥤ C ⥤ C)
    (P Q : Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}) {X X' : C} (β : X' ⟶ X) :=
  Convolution.transfer.{u, v, w} F P.obj Q.obj β


/-- The integral convolution presheaf of bundled additive coefficients. -/
abbrev convolutionPresheaf (F : C ⥤ C ⥤ C) (P Q : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u
    v w})) :=
  Convolution.presheaf.{u, v, w} F P.obj Q.obj

/-- The external coefficient tensor for bundled additive coefficients. -/
abbrev convolutionCoefficientModule (P Q : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})) :=
    Convolution.coefficientModule.{u, v, w} P.obj Q.obj
/-- The integer module of actual additive Hom groups used by convolution. -/
abbrev convolutionCorrespondenceModule := @Convolution.homModule.{u, v, w} C _ _
/-- The map on Hom labels induced by the underlying bifunctor. -/
abbrev convolutionCorrespondenceMap := @Convolution.bifunctorMap.{u, v} C _
/-- The curried integral convolution bifunctor on additive presheaves. -/
abbrev convolutionBifunctor := @Convolution.bifunctor.{u, v, w} C _ _

theorem coendPushforward_map_generator (F : C ⥤ C) [F.Additive] {P Q : (Cᵒᵖ ⥤+
    AddCommGrpCat.{max u v w})}
    (f : P ⟶ Q) (U Y : C) (s : (P.obj.obj (op Y))) (a : U ⟶ F.obj Y) :
    ((coendPushforward F).map f).hom.app (op U)
      (ParameterCoend.generator F P U Y s a) =
    ParameterCoend.generator F Q U Y (f.hom.app (op Y) s) a := by
  let V := additivePrecompose F
  have hm : (coendPushforward F).map f =
      coendPushforwardDesc F (f ≫ coendPushforwardUnit F Q) := by
    change coendPushforwardDesc F (f ≫ coendPushforwardUnit F Q ≫ V.map (𝟙 _)) =
      coendPushforwardDesc F (f ≫ coendPushforwardUnit F Q)
    rw [V.map_id, Category.comp_id]
  rw [hm]
  change (coendPushforwardDesc F (f ≫ coendPushforwardUnit F Q)).hom.app (op U)
      (ParameterCoend.generator F P U Y s a) = _
  rw [coendPushforwardDesc_app_generator]
  change ParameterCoend.transfer F Q a
    (ParameterCoend.generator F Q (F.obj Y) Y (f.hom.app (op Y) s) (𝟙 _)) = _
  exact (ParameterCoend.transfer_generator F Q a Y (f.hom.app (op Y) s) (𝟙 _)).trans
    (congrArg (ParameterCoend.generator F Q U Y (f.hom.app (op Y) s)) (Category.comp_id a))


variable (F : C ⥤ C ⥤ C) [F.Additive] [∀ Y, (F.obj Y).Additive]
variable (T : C)

local instance : (F.flip.obj T).Additive where
  map_add := by
    intro X Y f g
    change (F.map (f + g)).app T = (F.map f).app T + (F.map g).app T
    exact NatTrans.congr_app (F.map_add (f := f) (g := g)) T

/-- Postcomposition with the image of the parameter correspondence, extended linearly
    over `ℤ`. -/
def convolutionParameterComposition (U Y Z : C) :
    (ULift.{max u v w} (Z ⟶ T) ⊗[ℤ] ULift.{max u v w} (U ⟶ (F.obj Y).obj Z))
        →ₗ[ℤ]
      ULift.{max u v w} (U ⟶ (F.obj Y).obj T) := by
  let e (b : ULift.{max u v w} (Z ⟶ T)) :
      ULift.{max u v w} (U ⟶ (F.obj Y).obj Z) →+ ULift.{max u v w} (U ⟶ (F.obj
          Y).obj T) :=
    AddMonoidHom.mk' (fun a => ULift.up (a.down ≫ (F.obj Y).map b.down)) (by
      intro a a'
      apply congrArg ULift.up
      exact Preadditive.add_comp _ _ _ _ _ _)
  let f : ULift.{max u v w} (Z ⟶ T) →+
      (ULift.{max u v w} (U ⟶ (F.obj Y).obj Z) →ₗ[ℤ] ULift.{max u v w} (U ⟶
          (F.obj Y).obj T)) :=
    AddMonoidHom.mk' (fun b => (e b).toIntLinearMap) (by
      intro b b'
      apply LinearMap.ext
      intro a
      apply ULift.ext
      change a.down ≫ (F.obj Y).map (b.down + b'.down) =
        a.down ≫ (F.obj Y).map b.down + a.down ≫ (F.obj Y).map b'.down
      rw [Functor.map_add, Preadditive.comp_add])
  let g : ULift.{max u v w} (Z ⟶ T) →ₗ[ℤ]
      (ULift.{max u v w} (U ⟶ (F.obj Y).obj Z) →ₗ[ℤ] ULift.{max u v w} (U ⟶
          (F.obj Y).obj T)) :=
    { toFun := f
      map_add' := f.map_add
      map_smul' n b := (f.map_zsmul n b).trans (int_smul_eq_zsmul inferInstance n (f b)).symm }
  exact TensorProduct.lift g

/-- Send a convolution generator to the parameter coend by composing its two
    correspondences. -/
def convolutionParameterPairing (P : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})) (U Y Z : C) :
    ModuleCat.of ℤ (((P.obj.obj (op Y)) ⊗[ℤ] ULift.{max u v w} (Z ⟶ T)) ⊗[ℤ]
      ULift.{max u v w} (U ⟶ (F.obj Y).obj Z)) ⟶ ParameterCoend.sections (F.flip.obj
          T) P U :=
  let j : ModuleCat.of ℤ ((P.obj.obj (op Y)) ⊗[ℤ] ULift.{max u v w} (U ⟶ (F.obj
      Y).obj T)) ⟶
      ParameterCoend.sections (F.flip.obj T) P U :=
    coend.ι (ParameterCoend.diagram (F.flip.obj T) P U) Y
  ModuleCat.ofHom ((TensorProduct.map LinearMap.id (convolutionParameterComposition F T U
      Y Z)).comp
    (TensorProduct.assoc ℤ ((P.obj.obj (op Y))) (ULift.{max u v w} (Z ⟶ T))
      (ULift.{max u v w} (U ⟶ (F.obj Y).obj Z))).toLinearMap) ≫ j

/-- The pairing from a diagonal term of the convolution diagram to the parameter coend. -/
def convolutionParameterDiagramPairing (P : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}))
    (U : C) (YZ : C × C) :
    ((convolutionDiagram F P (represented T) U).obj (op YZ)).obj YZ ⟶
      ParameterCoend.sections (F.flip.obj T) P U :=
  convolutionParameterPairing F T P U YZ.1 YZ.2

set_option maxHeartbeats 1000000 in
-- The three bundled coefficient modules must be reduced to expose their pure tensors.
omit [F.Additive] in
theorem convolutionParameterPairing_dinatural (P : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}))
    (U : C) {YZ Y'Z' : C × C} (fg : YZ ⟶ Y'Z') :
    let D := convolutionDiagram F P (represented T) U
    (D.map fg.op).app YZ ≫ convolutionParameterDiagramPairing F T P U YZ =
      (D.obj (op Y'Z')).map fg ≫ convolutionParameterDiagramPairing F T P U Y'Z' := by
  obtain ⟨Y, Z⟩ := YZ
  obtain ⟨Y', Z'⟩ := Y'Z'
  let f := fg.1
  let g := fg.2
  let A := convolutionCoefficientModule P (represented T)
  let B := convolutionCorrespondenceModule F U
  let C := ModuleCat.of ℤ (((P.obj.obj (op Y')) ⊗[ℤ] ULift.{max u v w} (Z' ⟶ T))
      ⊗[ℤ]
    ULift.{max u v w} (U ⟶ (F.obj Y).obj Z))
  let H := ParameterCoend.sections (F.flip.obj T) P U
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
    change ParameterCoend.generator (F.flip.obj T) P U Y (ParameterCoend.action P f s)
        (a ≫ (F.obj Y).map (g ≫ b)) =
      ParameterCoend.generator (F.flip.obj T) P U Y' s
        ((a ≫ convolutionCorrespondenceMap F f g) ≫ (F.obj Y').map b)
    have ht := ParameterCoend.generator_transfer (F.flip.obj T) P f s
      (a ≫ (F.obj Y).map (g ≫ b))
    refine ht.trans (congrArg (ParameterCoend.generator (F.flip.obj T) P U Y' s) ?_)
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
def convolutionParameterHomApp (P : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})) (U : C) :
    convolutionSections F P (represented T) U ⟶
      ParameterCoend.sections (F.flip.obj T) P U :=
  coend.desc («F» := convolutionDiagram F P (represented T) U)
    (convolutionParameterDiagramPairing F T P U)
    (fun _ _ fg => convolutionParameterPairing_dinatural F T P U fg)

omit [F.Additive] in
@[simp]
private theorem convolutionParameterHomApp_generator (P : (Cᵒᵖ ⥤+
    AddCommGrpCat.{max u v w}))
    (U Y Z : C) (s : (P.obj.obj (op Y))) (b : Z ⟶ T) (a : U ⟶ (F.obj Y).obj Z) :
    convolutionParameterHomApp F T P U
      (convolutionGenerator F P (represented T) U Y Z s (ULift.up b) a) =
      ParameterCoend.generator (F.flip.obj T) P U Y s (a ≫ (F.obj Y).map b) := by
  change (coend.ι (convolutionDiagram F P (represented T) U) (Y, Z) ≫
    convolutionParameterHomApp F T P U) ((s ⊗ₜ[ℤ] ULift.up b) ⊗ₜ[ℤ] ULift.up a) = _
  have h := coend.ι_desc
    (convolutionParameterDiagramPairing F T P U)
    (fun _ _ fg => convolutionParameterPairing_dinatural F T P U fg)
    (Y, Z)
  exact ConcreteCategory.congr_hom h _

/-- The comparison from convolution with a right representable to additive coend
    pushforward. -/
def convolutionParameterHom (P : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})) :
    convolutionPresheaf F P (represented T) ⟶
      (coendPushforward (F.flip.obj T)).obj P :=
  ObjectProperty.homMk
    { app U := (forget₂ (ModuleCat.{max u v w} ℤ) AddCommGrpCat.{max u v w}).map
        (convolutionParameterHomApp F T P U.unop)
      naturality U U' β := by
        let V := forget₂ (ModuleCat.{max u v w} ℤ) AddCommGrpCat.{max u v w}
        change V.map (convolutionTransfer F P (represented T) β.unop) ≫
            V.map (convolutionParameterHomApp F T P U'.unop) =
          V.map (convolutionParameterHomApp F T P U.unop) ≫
            V.map (ParameterCoend.transfer (F.flip.obj T) P β.unop)
        rw [← V.map_comp, ← V.map_comp]
        apply congrArg V.map
        apply Convolution.sections_hom_ext
        intro Y Z s b a
        change ULift.{max u v w} (Z ⟶ T) at b
        obtain ⟨b⟩ := b
        let q := represented T
        let t : (q.obj.obj (op Z)) := ULift.up b
        let z := convolutionGenerator F P q U.unop Y Z s t a
        let m := convolutionParameterHomApp F T P U'.unop
        let n := ParameterCoend.transfer (F.flip.obj T) P β.unop
        change m (convolutionTransfer F P q β.unop z) =
          n (convolutionParameterHomApp F T P U.unop z)
        have h₁ := Convolution.transfer_generator F P.obj q.obj β.unop Y Z s t a
        have h₂ := convolutionParameterHomApp_generator F T P U'.unop Y Z s b (β.unop ≫ a)
        have h₃ := convolutionParameterHomApp_generator F T P U.unop Y Z s b a
        have h₄ := ParameterCoend.transfer_generator (F.flip.obj T) P β.unop Y s
          (a ≫ (F.obj Y).map b)
        have h₅ := congrArg (ParameterCoend.generator (F.flip.obj T) P U'.unop Y s)
          (Category.assoc β.unop a ((F.obj Y).map b))
        exact (congrArg m h₁).trans (h₂.trans
          (h₅.trans (h₄.symm.trans (congrArg n h₃).symm))) }

/-- The unit sends a section to the coend generator of the two identity correspondences. -/
def convolutionParameterUnit (P : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})) :
    P ⟶ (additivePrecompose (F.flip.obj T)).obj
      (convolutionPresheaf F P (represented T)) :=
  ObjectProperty.homMk
    { app Y := by
        let U := (F.obj Y.unop).obj T
        let j := convolutionInclusion F P (represented T) U Y.unop T
        let b : ((represented T).obj.obj (op T)) := ULift.up (𝟙 T)
        let a : ULift.{max u v w} (U ⟶ U) := ULift.up (𝟙 U)
        exact AddCommGrpCat.ofHom
          { toFun := fun s => convolutionGenerator F P (represented T)
              U Y.unop T s b (𝟙 U)
            map_zero' := by
              change j (((0 : (P.obj.obj (op Y.unop))) ⊗ₜ[ℤ] b) ⊗ₜ[ℤ] a) = 0
              rw [TensorProduct.zero_tmul, TensorProduct.zero_tmul, map_zero]
            map_add' := fun s s' =>
              Convolution.generator_add_left F P.obj (represented T).obj s s' b (𝟙 U) }
      naturality Y Y' β := by
        apply AddCommGrpCat.ext
        intro s
        change convolutionGenerator F P (represented T)
            ((F.obj Y'.unop).obj T) Y'.unop T (ParameterCoend.action P β.unop s)
                (ULift.up (𝟙 T)) (𝟙 _) =
          convolutionTransfer F P (represented T) ((F.map β.unop).app T)
            (convolutionGenerator F P (represented T)
              ((F.obj Y.unop).obj T) Y.unop T s (ULift.up (𝟙 T)) (𝟙 _))
        let q := represented T
        let t : (q.obj.obj (op T)) := ULift.up (𝟙 T)
        let a := (F.map β.unop).app T
        have h := Convolution.generator_transfer F P.obj q.obj β.unop (𝟙 T) s t
          (𝟙 ((F.obj Y'.unop).obj T))
        have h₁ : ParameterCoend.action q (𝟙 T) t = t := ConcreteCategory.congr_hom
            (q.obj.map_id (op T)) t
        have h₂ : 𝟙 ((F.obj Y'.unop).obj T) ≫ convolutionCorrespondenceMap F
            β.unop (𝟙 T) = a :=
          (Category.id_comp _).trans
            ((congrArg (a ≫ ·) ((F.obj Y.unop).map_id T)).trans (Category.comp_id a))
        have h₃ := Convolution.transfer_generator F P.obj q.obj a Y.unop T s t (𝟙 _)
        have h₄ := congrArg (convolutionGenerator F P q ((F.obj Y'.unop).obj T) Y.unop T s t)
          (Category.comp_id a)
        exact (congrArg (fun t₀ =>
          convolutionGenerator F P q ((F.obj Y'.unop).obj T) Y'.unop T
            (ParameterCoend.action P β.unop s) t₀ (𝟙 _)) h₁).symm.trans
          (h.trans ((congrArg (convolutionGenerator F P q ((F.obj Y'.unop).obj T) Y.unop T s t)
            h₂).trans (h₄.symm.trans h₃.symm))) }

/-- The reverse comparison induced by the coend unit with identity correspondences. -/
def convolutionParameterInv (P : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})) :
    (coendPushforward (F.flip.obj T)).obj P ⟶
      convolutionPresheaf F P (represented T) :=
  coendPushforwardDesc (F.flip.obj T) (convolutionParameterUnit F T P)

omit [∀ Y, (F.obj Y).Additive] in
@[simp]
private theorem convolutionParameterInv_generator (P : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u
    v w}))
    (U Y : C) (s : (P.obj.obj (op Y))) (a : U ⟶ (F.obj Y).obj T) :
    (convolutionParameterInv F T P).hom.app (op U)
      (ParameterCoend.generator (F.flip.obj T) P U Y s a) =
    convolutionGenerator F P (represented T) U Y T s (ULift.up (𝟙 T)) a := by
  let q := represented T
  let t : (q.obj.obj (op T)) := ULift.up (𝟙 T)
  let G := F.flip.obj T
  have h := coendPushforwardDesc_app_generator G (convolutionParameterUnit F T P) U Y s a
  change (convolutionParameterInv F T P).hom.app (op U)
      (ParameterCoend.generator G P U Y s a) =
    convolutionTransfer F P q a
      (convolutionGenerator F P q (G.obj Y) Y T s t (𝟙 _)) at h
  exact h.trans ((Convolution.transfer_generator F P.obj q.obj a Y T s t (𝟙 _)).trans
    (congrArg (convolutionGenerator F P q U Y T s t) (Category.comp_id a)))

/-- Tensoring with a represented right parameter agrees with the original coend pushforward. -/
def convolutionParameterIso (P : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})) :
    convolutionPresheaf F P (represented T) ≅
      (coendPushforward (F.flip.obj T)).obj P where
  hom := convolutionParameterHom F T P
  inv := convolutionParameterInv F T P
  hom_inv_id := by
    apply Convolution.presheaf_hom_ext
    intro U Y Z s b a
    change ULift.{max u v w} (Z ⟶ T) at b
    obtain ⟨b⟩ := b
    let q := represented T
    let t : (q.obj.obj (op Z)) := ULift.up b
    let t₀ : (q.obj.obj (op T)) := ULift.up (𝟙 T)
    let z := convolutionGenerator F P q U Y Z s t a
    let m := (convolutionParameterInv F T P).hom.app (op U)
    let a' := a ≫ (F.obj Y).map b
    change m (convolutionParameterHomApp F T P U z) = z
    have h₁ := convolutionParameterHomApp_generator F T P U Y Z s b a
    have h₂ := convolutionParameterInv_generator F T P U Y s a'
    have ht : ParameterCoend.action q b t₀ = t := by
      change ULift.up (b ≫ 𝟙 T) = ULift.up b
      exact congrArg ULift.up (Category.comp_id b)
    have hs : ParameterCoend.action P (𝟙 Y) s = s :=
      ConcreteCategory.congr_hom (P.obj.map_id (op Y)) s
    have h := Convolution.generator_transfer F P.obj q.obj (𝟙 Y) b s t₀ a
    have h' : a ≫ convolutionCorrespondenceMap F (𝟙 Y) b = a' := by
      change a ≫ (F.map (𝟙 Y)).app Z ≫ (F.obj Y).map b = _
      rw [show (F.map (𝟙 Y)).app Z = 𝟙 _ from NatTrans.congr_app (F.map_id Y) Z,
        Category.id_comp]
    have h₃ : z = convolutionGenerator F P q U Y T s t₀ a' :=
      ((congrArg₂ (fun s₀ t₁ => convolutionGenerator F P q U Y Z s₀ t₁ a) hs
          ht).symm.trans h).trans
        (congrArg (convolutionGenerator F P q U Y T s t₀) h')
    exact (congrArg m h₁).trans (h₂.trans h₃.symm)
  inv_hom_id := by
    apply ParameterCoend.presheaf_hom_ext
    intro U Y s a
    let G := F.flip.obj T
    let z := ParameterCoend.generator G P U Y s a
    let m := convolutionParameterHomApp F T P U
    change m ((convolutionParameterInv F T P).hom.app (op U) z) = z
    have h₁ := convolutionParameterInv_generator F T P U Y s a
    have h₂ := convolutionParameterHomApp_generator F T P U Y T s (𝟙 T) a
    have h₃ : a ≫ (F.obj Y).map (𝟙 T) = a :=
      (congrArg (a ≫ ·) ((F.obj Y).map_id T)).trans (Category.comp_id a)
    exact (congrArg m h₁).trans (h₂.trans (congrArg (ParameterCoend.generator G P U Y
        s) h₃))

@[simp]
theorem convolutionParameterIso_hom_generator (P : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}))
    (U Y Z : C) (s : (P.obj.obj (op Y))) (b : Z ⟶ T) (a : U ⟶ (F.obj Y).obj Z) :
    (convolutionParameterIso F T P).hom.hom.app (op U)
      (convolutionGenerator F P (represented T) U Y Z s (ULift.up b) a) =
      ParameterCoend.generator (F.flip.obj T) P U Y s (a ≫ (F.obj Y).map b) :=
  convolutionParameterHomApp_generator F T P U Y Z s b a

/-- The comparison identifies the unit on each literal generator with the pushforward unit. -/
theorem convolutionParameterIso_unit (P : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})) :
    convolutionParameterUnit F T P ≫
        (additivePrecompose (F.flip.obj T)).map (convolutionParameterIso F T P).hom =
      coendPushforwardUnit (F.flip.obj T) P := by
  apply ObjectProperty.hom_ext
  ext Y s
  change (convolutionParameterIso F T P).hom.hom.app (op ((F.obj Y.unop).obj T))
    (convolutionGenerator F P (represented T) ((F.obj Y.unop).obj T)
      Y.unop T s (ULift.up (𝟙 T)) (𝟙 _)) = _
  have h := convolutionParameterIso_hom_generator F T P
    ((F.obj Y.unop).obj T) Y.unop T s (𝟙 T) (𝟙 _)
  have h' : 𝟙 ((F.obj Y.unop).obj T) ≫ (F.obj Y.unop).map (𝟙 T) = 𝟙 _ :=
    (Category.id_comp _).trans ((F.obj Y.unop).map_id T)
  exact h.trans (congrArg
    (ParameterCoend.generator (F.flip.obj T) P ((F.obj Y.unop).obj T) Y.unop s) h')

omit [∀ Y, (F.obj Y).Additive] in
/-- Convolution with the right represented parameter is naturally the coend pushforward. -/
def convolutionParameterNatIso :
    (convolutionBifunctor F).flip.obj (represented T) ≅
      coendPushforward (F.flip.obj T) :=
  NatIso.ofComponents (convolutionParameterIso F T) (fun {P Q} f => by
    apply Convolution.presheaf_hom_ext
    intro U Y Z s b a
    change ULift.{max u v w} (Z ⟶ T) at b
    obtain ⟨b⟩ := b
    change (convolutionParameterIso F T Q).hom.hom.app (op U)
        ((Convolution.map F f (𝟙 (represented T))).hom.app (op U)
          (convolutionGenerator F P (represented T) U Y Z s (ULift.up b) a)) =
      ((coendPushforward (F.flip.obj T)).map f).hom.app (op U)
        ((convolutionParameterIso F T P).hom.hom.app (op U)
          (convolutionGenerator F P (represented T) U Y Z s (ULift.up b) a))
    let q := represented T
    let t : (q.obj.obj (op Z)) := ULift.up b
    let z := convolutionGenerator F P q U Y Z s t a
    let m := (convolutionParameterIso F T Q).hom.hom.app (op U)
    let n := ((coendPushforward (F.flip.obj T)).map f).hom.app (op U)
    let w := (convolutionParameterIso F T P).hom.hom.app (op U)
    have ht : (𝟙 q : q ⟶ q).hom.app (op Z) t = t := rfl
    have h₁ := Convolution.map_generator F f (𝟙 q) U Y Z s t a
    have h₂ := congrArg (fun t₀ => convolutionGenerator F Q q U Y Z
      (f.hom.app (op Y) s) t₀ a) ht
    have h₃ := convolutionParameterIso_hom_generator F T Q U Y Z (f.hom.app (op Y) s) b a
    have h₄ := convolutionParameterIso_hom_generator F T P U Y Z s b a
    have h₅ := coendPushforward_map_generator (F.flip.obj T) f U Y s (a ≫ (F.obj Y).map b)
    change m ((Convolution.map F f (𝟙 q)).hom.app (op U) z) = n (w z)
    exact (congrArg m (h₁.trans h₂)).trans (h₃.trans (h₅.symm.trans (congrArg n
        h₄).symm)))

end CategoryTheory.Preadditive.ConvolutionRepresented
