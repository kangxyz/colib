/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.Coefficients
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.PushforwardExactness
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.Representable
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Maps of the integral coend pushforward -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

set_option quotPrecheck false in
local notation "PST(" K ")" => TransferCoefficients K

variable {G H : Cor k ⥤ Cor k} [G.Additive] [H.Additive]

/-- A natural map of parameters acts by precomposition on sections. -/
def additivePrecomposeMap (f : G ⟶ H) : additivePrecompose H ⟶ additivePrecompose G where
  app P := ObjectProperty.homMk (Functor.whiskerRight (NatTrans.op f) P.obj)
  naturality P Q g := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    change g.hom.app (H.op.obj X) ≫ Q.obj.map (f.app X.unop).op =
      P.obj.map (f.app X.unop).op ≫ g.hom.app (G.op.obj X)
    exact (g.hom.naturality (f.app X.unop).op).symm

/-- The native map of coend pushforwards is the mate of the section map. -/
def coendPushforwardParameterMap (f : G ⟶ H) : coendPushforward G ⟶ coendPushforward H :=
  (conjugateEquiv (coendPushforwardAdjunction H) (coendPushforwardAdjunction G)).symm
    (additivePrecomposeMap f)

/-- The mate acts on the literal coend generators by postcomposition. -/
theorem coendPushforwardParameterMap_generator (f : G ⟶ H) (P : PST(k))
    (X Y : Cor k) (s : sections P Y) (a : X ⟶ G.obj Y) :
    ((coendPushforwardParameterMap f).app P).hom.app (op X)
      (parameterTensorGenerator G P X Y s a) =
    parameterTensorGenerator H P X Y s (a ≫ f.app Y) := by
  let m := (coendPushforwardParameterMap f).app P
  let z := parameterTensorGenerator G P (G.obj Y) Y s (𝟙 _)
  have h := unit_conjugateEquiv_symm (coendPushforwardAdjunction H)
    (coendPushforwardAdjunction G) (additivePrecomposeMap f) P
  rw [coendPushforwardAdjunction_unit_app, coendPushforwardAdjunction_unit_app] at h
  have hv := ConcreteCategory.congr_hom
    (congrArg (fun b => b.hom.app (op Y)) h) s
  change parameterTensorTransfer H P (f.app Y)
      (parameterTensorGenerator H P (H.obj Y) Y s (𝟙 _)) =
    m.hom.app (op (G.obj Y)) z at hv
  have hn := ConcreteCategory.congr_hom (transfer_naturality m a) z
  change m.hom.app (op X) (parameterTensorTransfer G P a z) =
    parameterTensorTransfer H P a (m.hom.app (op (G.obj Y)) z) at hn
  rw [show z = parameterTensorGenerator G P (G.obj Y) Y s (𝟙 _) from rfl,
    parameterTensorTransfer_generator, Category.comp_id, ← hv,
    parameterTensorTransfer_generator, Category.comp_id, parameterTensorTransfer_generator] at hn
  exact hn

/-- The mate of a map of parameters acts on the represented object by its original component. -/
theorem coendPushforwardRepresentableIso_parameterMap (f : G ⟶ H) (X : Cor k) :
    (coendPushforwardParameterMap f).app ((representableLarge k).obj X) ≫
        (coendPushforwardRepresentableIso H X).hom =
      (coendPushforwardRepresentableIso G X).hom ≫ (representableLarge k).map (f.app X) := by
  apply parameterTensorPresheaf_hom_ext
  intro U V s a
  change ULift.{u + 1} (V ⟶ X) at s
  obtain ⟨b⟩ := s
  let P := (representableLarge k).obj X
  let m := (coendPushforwardParameterMap f).app P
  let h := coendPushforwardRepresentableHom G X
  let h' := coendPushforwardRepresentableHom H X
  let n := (representableLarge k).map (f.app X)
  let z := parameterTensorGenerator G P U V (ULift.up b) a
  change h'.hom.app (op U) (m.hom.app (op U) z) = n.hom.app (op U) (h.hom.app (op U) z)
  have h₁ := coendPushforwardParameterMap_generator f P U V (ULift.up b) a
  have h₂ := coendPushforwardRepresentableHom_app H X U V b (a ≫ f.app V)
  have h₃ := coendPushforwardRepresentableHom_app G X U V b a
  have h₄ := representableLarge_map_app_apply k (f.app X) (a ≫ G.map b)
  have hh : (a ≫ f.app V) ≫ H.map b = (a ≫ G.map b) ≫ f.app X := by
    simp only [Category.assoc, f.naturality b]
  exact (congrArg (h'.hom.app (op U)) h₁).trans
    (h₂.trans ((congrArg ULift.up hh).trans
      (h₄.symm.trans (congrArg (n.hom.app (op U)) h₃).symm)))

/-- The canonical pushforward isomorphism of parameter functors agrees with their left mate. -/
theorem coendPushforwardNatIso_hom_eq_parameterMap {G H : Cor k ⥤ Cor k}
    [G.Additive] [H.Additive] (e : G ≅ H) :
    (coendPushforwardNatIso G e).hom = coendPushforwardParameterMap e.hom := by
  let b := additivePrecomposeNatIso G e
  let A := coendPushforwardAdjunction G
  let B := coendPushforwardAdjunction H
  have he : additivePrecomposeMap e.hom = b.inv := by
    apply NatTrans.ext
    funext P
    apply ObjectProperty.hom_ext
    rfl
  apply NatTrans.ext
  funext P
  let f := (coendPushforwardNatIso G e).hom.app P
  let g := (coendPushforwardParameterMap e.hom).app P
  have hf : A.homEquiv P ((coendPushforward H).obj P) f ≫ b.hom.app _ = B.unit.app P := by
    have h := Adjunction.homEquiv_leftAdjointUniq_hom_app (A.ofNatIsoRight b) B P
    rw [Adjunction.homEquiv_ofNatIsoRight_apply] at h
    exact h
  have hg : B.unit.app P ≫ b.inv.app _ = A.homEquiv P ((coendPushforward H).obj P) g := by
    rw [← he, Adjunction.homEquiv_unit]
    exact unit_conjugateEquiv_symm B A (additivePrecomposeMap e.hom) P
  apply (A.homEquiv P ((coendPushforward H).obj P)).injective
  rw [← hg, ← hf, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

/-- The coend comparison commutes with a square of the original parameter maps. -/
theorem coendPushforwardNatIso_parameterMap
    {G H G' H' : Cor k ⥤ Cor k} [G.Additive] [H.Additive] [G'.Additive] [H'.Additive]
    (e : G ≅ G') (e' : H ≅ H') (f : G ⟶ H) (f' : G' ⟶ H')
    (h : f ≫ e'.hom = e.hom ≫ f') :
    coendPushforwardParameterMap f ≫ (coendPushforwardNatIso H e').hom =
      (coendPushforwardNatIso G e).hom ≫ coendPushforwardParameterMap f' := by
  rw [coendPushforwardNatIso_hom_eq_parameterMap, coendPushforwardNatIso_hom_eq_parameterMap]
  apply NatTrans.ext
  funext P
  apply parameterTensorPresheaf_hom_ext
  intro X Y p a
  change ((coendPushforwardParameterMap e'.hom).app P).hom.app (op X)
      (((coendPushforwardParameterMap f).app P).hom.app (op X)
        (parameterTensorGenerator G P X Y p a)) =
    ((coendPushforwardParameterMap f').app P).hom.app (op X)
      (((coendPushforwardParameterMap e.hom).app P).hom.app (op X)
        (parameterTensorGenerator G P X Y p a))
  simp only [coendPushforwardParameterMap_generator, Category.assoc]
  exact congrArg (fun b => parameterTensorGenerator H' P X Y p (a ≫ b))
    (NatTrans.congr_app h Y)

end AlgebraicGeometry.PresheafWithTransfers
