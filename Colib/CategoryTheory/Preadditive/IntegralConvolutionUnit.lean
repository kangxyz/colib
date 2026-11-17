/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Preadditive.IntegralConvolutionRepresented
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# The represented convolution unit

A right unit for the correspondence bifunctor yields the right unit
given by its original representable.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace CategoryTheory.Preadditive.ConvolutionRepresented

variable {C : Type u} [Category.{v} C] [Preadditive C]
open CategoryTheory.Preadditive.ParameterCoend

variable (F : C ⥤ C ⥤ C) [F.Additive] [∀ Y, (F.obj Y).Additive]
variable (T : C) (e : F.flip.obj T ≅ 𝟭 (C))

local instance : (F.flip.obj T).Additive where
  map_add := by
    intro X Y f g
    change (F.map (f + g)).app T = (F.map f).app T + (F.map g).app T
    exact NatTrans.congr_app (F.map_add (f := f) (g := g)) T

/-- Pushforward along a functor identified with the identity. -/
def parameterUnitor :
    coendPushforward (F.flip.obj T) ≅ 𝟭 ((Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})) :=
  ((coendPushforwardAdjunction (F.flip.obj T)).ofNatIsoRight
    (additivePrecomposeNatIso (F.flip.obj T) e ≪≫ additivePrecomposeIdIso)).leftAdjointUniq
      Adjunction.id

omit [∀ Y, (F.obj Y).Additive] in
private theorem parameterUnitor_hom_generator
    (P : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})) (U Y : C) (s : (P.obj.obj (op Y))) (a
        : U ⟶ (F.flip.obj T).obj Y) :
    ((parameterUnitor F T e).hom.app P).hom.app (op U)
        (ParameterCoend.generator (F.flip.obj T) P U Y s a) =
      ParameterCoend.action P (a ≫ e.hom.app Y) s := by
  let G := F.flip.obj T
  let d := additivePrecomposeNatIso G e ≪≫ additivePrecomposeIdIso
  let A := coendPushforwardAdjunction G
  let h := (parameterUnitor F T e).hom.app P
  have he : (A.ofNatIsoRight d).homEquiv P P h = 𝟙 P :=
    Adjunction.homEquiv_leftAdjointUniq_hom_app (A.ofNatIsoRight d) Adjunction.id P
  rw [Adjunction.homEquiv_ofNatIsoRight_apply] at he
  have he' : A.homEquiv P P h = d.inv.app P := by
    have hh := congrArg (· ≫ d.inv.app P) he
    simpa only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id, Category.id_comp]
        using hh
  let θ : P ⟶ (additivePrecompose G).obj P := d.inv.app P
  let h' : ParameterCoend.presheaf G P ⟶ P := coendPushforwardDesc G θ
  have hh : h = h' := by
    apply (A.homEquiv P P).injective
    rw [he']
    change d.inv.app P = coendPushforwardHomEquiv G P P
      ((coendPushforwardHomEquiv G P P).symm (d.inv.app P))
    exact ((coendPushforwardHomEquiv G P P).apply_symm_apply _).symm
  let z := ParameterCoend.generator G P U Y s a
  have h₀ : h.hom.app (op U) z = h'.hom.app (op U) z := by
    exact congrArg (fun m : ParameterCoend.presheaf G P ⟶ P => m.hom.app (op U) z) hh
  have h₁ : h'.hom.app (op U) z = ParameterCoend.action P a (θ.hom.app (op Y) s) :=
    coendPushforwardDesc_app_generator G θ U Y s a
  have h₂ : θ.hom.app (op Y) s = ParameterCoend.action P (e.hom.app Y) s := by
    change ((𝟙 _ ≫ P.obj.map (e.hom.app Y).op : _ ⟶ _) s) = _
    rw [Category.id_comp]
  have h₃ : ParameterCoend.action P a (ParameterCoend.action P (e.hom.app Y) s) =
      ParameterCoend.action P (a ≫ e.hom.app Y) s := by
    change P.obj.map a.op (P.obj.map (e.hom.app Y).op s) =
      P.obj.map (a ≫ e.hom.app Y).op s
    rw [op_comp, P.obj.map_comp]
    rfl
  exact h₀.trans (h₁.trans ((congrArg (ParameterCoend.action P a) h₂).trans h₃))

/-- The original correspondence right unitor induces the represented convolution right
    unitor. -/
def convolutionRightUnitIso :
    (convolutionBifunctor F).flip.obj (represented T) ≅ 𝟭 ((Cᵒᵖ ⥤+
        AddCommGrpCat.{max u v w})) :=
  convolutionParameterNatIso F T ≪≫ parameterUnitor F T e

/-- The original right unitor transfers a section along the correspondence label,
including its represented parameter. -/
theorem convolutionRightUnitIso_hom_generator
    (P : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})) (U Y Z : C) (s : (P.obj.obj (op Y)))
        (b : Z ⟶ T) (a : U ⟶ (F.obj Y).obj Z) :
    ((convolutionRightUnitIso F T e).hom.app P).hom.app (op U)
      (convolutionGenerator F P (represented T) U Y Z s (ULift.up b) a) =
        ParameterCoend.action P (a ≫ (F.obj Y).map b ≫ e.hom.app Y) s := by
  let h := (parameterUnitor F T e).hom.app P
  change h.hom.app (op U)
    ((convolutionParameterIso F T P).hom.hom.app (op U)
      (convolutionGenerator F P (represented T) U Y Z s (ULift.up b) a)) = _
  rw [convolutionParameterIso_hom_generator, parameterUnitor_hom_generator, Category.assoc]

end CategoryTheory.Preadditive.ConvolutionRepresented
