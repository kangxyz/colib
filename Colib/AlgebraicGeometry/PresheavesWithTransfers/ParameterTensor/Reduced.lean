/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ContractionFunctor
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ParameterTensor.Adjunction
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Tensor with the reduced transfer torus

The graph of the torus unit defines a restriction on the right.
Its left mate gives the original unit inclusion in the parameter
tensor. The reduced tensor is its cokernel, with the original
contraction kernel as right adjoint.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme SmoothSite.Contraction

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "Bₖ" => SmoothSite.base (Spec (CommRingCat.of k))
local notation "Gₘ" => SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k))
local notation "L₀" => parameterTensorFunctor Bₖ
local notation "L₁" => parameterTensorFunctor Gₘ
local notation "a₀" => parameterTensorAdjunction Bₖ
local notation "a₁" => parameterTensorAdjunction Gₘ

/-- The original parameter restriction on the coefficient functors. -/
def parameterPullbackNatTrans {V W : SmoothSite (Spec (.of k))}
    [GeometricallyIntegral V.hom] [GeometricallyIntegral W.hom] (f : V ⟶ W) :
    (withParameterFunctor W : PresheafWithTransfers.{u + 1} k ⥤ _) ⟶
      withParameterFunctor V where
  app P := parameterPullback P f
  naturality _ _ g := (parameterPullback_coefficient_naturality g f).symm

/-- Restriction to the literal unit before identifying base-product coordinates. -/
abbrev torusParameterRestriction :
    (withParameterFunctor Gₘ : PresheafWithTransfers.{u + 1} k ⥤ _) ⟶
      withParameterFunctor Bₖ :=
  parameterPullbackNatTrans k (SmoothSite.torusOne (Spec (.of k)))

/-- Constants along the actual base projection. -/
abbrev torusParameterConstant :
    (withParameterFunctor Bₖ : PresheafWithTransfers.{u + 1} k ⥤ _) ⟶
      withParameterFunctor Gₘ :=
  parameterPullbackNatTrans k (toBase Gₘ)

/-- The left mate of restriction to the literal unit. -/
@[no_expose]
def torusParameterTensorUnit : L₀ ⟶ L₁ :=
  (conjugateEquiv a₁ a₀).symm (torusParameterRestriction k)

/-- The left mate of the actual constant section. -/
@[no_expose]
def torusParameterTensorProjection : L₁ ⟶ L₀ :=
  (conjugateEquiv a₀ a₁).symm (torusParameterConstant k)

/-- The left tensor unit and projection split on the original maps. -/
theorem torusParameterTensorUnit_projection :
    torusParameterTensorUnit k ≫ torusParameterTensorProjection k = 𝟙 _ := by
  unfold torusParameterTensorUnit torusParameterTensorProjection
  apply conjugateEquiv_symm_comm a₀ a₁
  apply NatTrans.ext
  funext P
  exact torusConstant_unit P

/-- Transposition carries the left unit condition to the right unit condition. -/
theorem torusParameterTensorUnit_homEquiv
    {P Q : PresheafWithTransfers.{u + 1} k} (f : (L₁).obj P ⟶ Q) :
    (a₀).homEquiv P Q ((torusParameterTensorUnit k).app P ≫ f) =
      (a₁).homEquiv P Q f ≫ torusUnit Q := by
  let R₀ : PresheafWithTransfers.{u + 1} k ⥤ PresheafWithTransfers.{u + 1} k :=
    withParameterFunctor Bₖ
  let R₁ : PresheafWithTransfers.{u + 1} k ⥤ PresheafWithTransfers.{u + 1} k :=
    withParameterFunctor Gₘ
  let u := torusParameterRestriction k
  let i := torusParameterTensorUnit k
  have h : (a₁).unit.app P ≫ u.app ((L₁).obj P) =
      (a₀).unit.app P ≫ R₀.map (i.app P) :=
    unit_conjugateEquiv_symm a₁ a₀ u P
  change (a₀).homEquiv P Q (i.app P ≫ f) = (a₁).homEquiv P Q f ≫ u.app Q
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, R₀.map_comp]
  calc
    _ = ((a₀).unit.app P ≫ R₀.map (i.app P)) ≫ R₀.map f := (Category.assoc _ _ _).symm
    _ = ((a₁).unit.app P ≫ u.app ((L₁).obj P)) ≫ R₀.map f :=
      congrArg (· ≫ R₀.map f) h.symm
    _ = (a₁).unit.app P ≫ (u.app ((L₁).obj P) ≫ R₀.map f) := Category.assoc _ _ _
    _ = (a₁).unit.app P ≫ (R₁.map f ≫ u.app Q) :=
      congrArg ((a₁).unit.app P ≫ ·) (u.naturality f).symm
    _ = _ := (Category.assoc _ _ _).symm

/-- Transposition carries the left projection to the original right
constant section. -/
theorem torusParameterTensorProjection_homEquiv
    {P Q : PresheafWithTransfers.{u + 1} k} (f : (L₀).obj P ⟶ Q) :
    (a₁).homEquiv P Q ((torusParameterTensorProjection k).app P ≫ f) =
      (a₀).homEquiv P Q f ≫ torusConstant Q := by
  let R₀ : PresheafWithTransfers.{u + 1} k ⥤ PresheafWithTransfers.{u + 1} k :=
    withParameterFunctor Bₖ
  let R₁ : PresheafWithTransfers.{u + 1} k ⥤ PresheafWithTransfers.{u + 1} k :=
    withParameterFunctor Gₘ
  let c := torusParameterConstant k
  let r := torusParameterTensorProjection k
  have h : (a₀).unit.app P ≫ c.app ((L₀).obj P) =
      (a₁).unit.app P ≫ R₁.map (r.app P) :=
    unit_conjugateEquiv_symm a₀ a₁ c P
  change (a₁).homEquiv P Q (r.app P ≫ f) = (a₀).homEquiv P Q f ≫ c.app Q
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, R₁.map_comp]
  calc
    _ = ((a₁).unit.app P ≫ R₁.map (r.app P)) ≫ R₁.map f := (Category.assoc _ _ _).symm
    _ = ((a₀).unit.app P ≫ c.app ((L₀).obj P)) ≫ R₁.map f :=
      congrArg (· ≫ R₁.map f) h.symm
    _ = (a₀).unit.app P ≫ (c.app ((L₀).obj P) ≫ R₁.map f) := Category.assoc _ _ _
    _ = (a₀).unit.app P ≫ (R₀.map f ≫ c.app Q) :=
      congrArg ((a₀).unit.app P ≫ ·) (c.naturality f).symm
    _ = _ := (Category.assoc _ _ _).symm

/-- The induced map of the actual unit cokernels. -/
@[no_expose]
def reducedParameterTensorMap {P Q : PresheafWithTransfers.{u + 1} k} (f : P ⟶ Q) :
    cokernel ((torusParameterTensorUnit k).app P) ⟶
      cokernel ((torusParameterTensorUnit k).app Q) :=
  cokernel.map _ _ ((L₀).map f) ((L₁).map f) ((torusParameterTensorUnit k).naturality f).symm

@[reassoc]
private theorem reducedParameterTensorMap_π {P Q : PresheafWithTransfers.{u + 1} k} (f : P ⟶ Q) :
    cokernel.π ((torusParameterTensorUnit k).app P) ≫ reducedParameterTensorMap k f =
      (L₁).map f ≫ cokernel.π ((torusParameterTensorUnit k).app Q) :=
  cokernel.π_desc _ _ _

/-- The cokernel of the actual tensor unit. -/
abbrev reducedParameterTensorFunctor :
    PresheafWithTransfers.{u + 1} k ⥤ PresheafWithTransfers.{u + 1} k where
  obj P := cokernel ((torusParameterTensorUnit k).app P)
  map f := reducedParameterTensorMap k f
  map_id P := by
    apply (cancel_epi (cokernel.π ((torusParameterTensorUnit k).app P))).mp
    rw [reducedParameterTensorMap_π, CategoryTheory.Functor.map_id, Category.id_comp,
      Category.comp_id]
  map_comp {P _ _} f g := by
    apply (cancel_epi (cokernel.π ((torusParameterTensorUnit k).app P))).mp
    rw [reducedParameterTensorMap_π, reducedParameterTensorMap_π_assoc,
      reducedParameterTensorMap_π, CategoryTheory.Functor.map_comp, Category.assoc]

/-- The original quotient from the unreduced tensor. -/
@[no_expose]
def reducedParameterTensorQuotient : L₁ ⟶ reducedParameterTensorFunctor k where
  app P := cokernel.π ((torusParameterTensorUnit k).app P)
  naturality _ _ f := (reducedParameterTensorMap_π k f).symm

@[simp]
theorem reducedParameterTensorQuotient_app (P : PresheafWithTransfers.{u + 1} k) :
    (reducedParameterTensorQuotient k).app P =
      cokernel.π ((torusParameterTensorUnit k).app P) := by
  unfold reducedParameterTensorQuotient
  rfl

/-- The original tensor unit is killed by the reduced quotient. -/
@[reassoc]
theorem torusParameterTensorUnit_quotient (P : PresheafWithTransfers.{u + 1} k) :
    (torusParameterTensorUnit k).app P ≫ (reducedParameterTensorQuotient k).app P = 0 :=
  cokernel.condition ((torusParameterTensorUnit k).app P)

/-- The reduced quotient has the section determined by the original
unit and projection. -/
@[no_expose]
def reducedParameterTensorSection : reducedParameterTensorFunctor k ⟶ L₁ := by
  let i := torusParameterTensorUnit k
  let r := torusParameterTensorProjection k
  let s (P : PresheafWithTransfers.{u + 1} k) :
      cokernel (i.app P) ⟶ (L₁).obj P :=
    cokernel.desc (i.app P) (𝟙 _ - r.app P ≫ i.app P) (by
      have h := NatTrans.congr_app (torusParameterTensorUnit_projection k) P
      change i.app P ≫ r.app P = 𝟙 _ at h
      rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc, h,
        Category.id_comp, sub_self])
  have hs (P : PresheafWithTransfers.{u + 1} k) :
      cokernel.π (i.app P) ≫ s P = 𝟙 _ - r.app P ≫ i.app P :=
    cokernel.π_desc _ _ _
  unfold reducedParameterTensorFunctor
  refine { app := s, naturality := ?_ }
  intro P Q f
  change reducedParameterTensorMap k f ≫ s Q = s P ≫ (L₁).map f
  apply (cancel_epi (cokernel.π (i.app P))).mp
  have hp := reducedParameterTensorMap_π k f
  change cokernel.π (i.app P) ≫ reducedParameterTensorMap k f =
    (L₁).map f ≫ cokernel.π (i.app Q) at hp
  calc
    _ = (L₁).map f ≫ (cokernel.π (i.app Q) ≫ s Q) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ s Q) hp).trans (Category.assoc _ _ _))
    _ = (L₁).map f ≫ (𝟙 _ - r.app Q ≫ i.app Q) :=
      congrArg ((L₁).map f ≫ ·) (hs Q)
    _ = (𝟙 _ - r.app P ≫ i.app P) ≫ (L₁).map f := by
      rw [Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id, Category.id_comp,
        ← Category.assoc ((L₁).map f), r.naturality f, Category.assoc, i.naturality f,
        ← Category.assoc]
    _ = _ := (congrArg (· ≫ (L₁).map f) (hs P).symm).trans (Category.assoc _ _ _)

/-- The section realizes the complementary unit projector. -/
@[reassoc]
theorem reducedParameterTensorQuotient_section (P : PresheafWithTransfers.{u + 1} k) :
    (reducedParameterTensorQuotient k).app P ≫ (reducedParameterTensorSection k).app P =
      𝟙 _ - (torusParameterTensorProjection k).app P ≫ (torusParameterTensorUnit k).app P := by
  unfold reducedParameterTensorQuotient reducedParameterTensorSection
  exact cokernel.π_desc ((torusParameterTensorUnit k).app P) _ _

/-- The section and the actual reduced quotient split. -/
@[reassoc]
theorem reducedParameterTensorSection_quotient (P : PresheafWithTransfers.{u + 1} k) :
    (reducedParameterTensorSection k).app P ≫ (reducedParameterTensorQuotient k).app P =
      𝟙 _ := by
  let q := (reducedParameterTensorQuotient k).app P
  apply (cancel_epi (cokernel.π ((torusParameterTensorUnit k).app P))).mp
  change q ≫ ((reducedParameterTensorSection k).app P ≫ q) = q ≫ 𝟙 _
  calc
    _ = (𝟙 _ - (torusParameterTensorProjection k).app P ≫
        (torusParameterTensorUnit k).app P) ≫ q :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ q) (reducedParameterTensorQuotient_section k P))
    _ = q := by
      rw [Preadditive.sub_comp, Category.id_comp, Category.assoc,
        torusParameterTensorUnit_quotient, comp_zero, sub_zero]
    _ = _ := (Category.comp_id _).symm

private def reducedTensorHomEquiv (P Q : PresheafWithTransfers.{u + 1} k) :
    ((reducedParameterTensorFunctor k).obj P ⟶ Q) ≃ (P ⟶ contractionKernel Q) := by
  let i := (torusParameterTensorUnit k).app P
  let p := cokernel.π i
  let u := torusUnit Q
  let j := kernel.ι u
  let e := (a₁).homEquiv P Q
  have hu (f : cokernel i ⟶ Q) : e (p ≫ f) ≫ u = 0 := by
    rw [← torusParameterTensorUnit_homEquiv k, ← Category.assoc, cokernel.condition, zero_comp,
      Adjunction.homAddEquiv_zero]
  have hi (g : P ⟶ kernel u) : i ≫ e.symm (g ≫ j) = 0 := by
    apply ((a₀).homEquiv P Q).injective
    rw [torusParameterTensorUnit_homEquiv k, Equiv.apply_symm_apply, Category.assoc,
      kernel.condition, comp_zero, Adjunction.homAddEquiv_zero]
  refine
    { toFun := fun f => kernel.lift u (e (p ≫ f)) (hu f)
      invFun := fun g => cokernel.desc i (e.symm (g ≫ j)) (hi g)
      left_inv := ?_
      right_inv := ?_ }
  · intro f
    apply (cancel_epi p).mp
    rw [cokernel.π_desc, kernel.lift_ι, Equiv.symm_apply_apply]
  · intro g
    apply (cancel_mono j).mp
    rw [kernel.lift_ι, cokernel.π_desc, Equiv.apply_symm_apply]

private theorem reducedTensorHomEquiv_ι (P Q : PresheafWithTransfers.{u + 1} k)
    (f : (reducedParameterTensorFunctor k).obj P ⟶ Q) :
    reducedTensorHomEquiv k P Q f ≫ kernel.ι (torusUnit Q) =
      (a₁).homEquiv P Q (cokernel.π ((torusParameterTensorUnit k).app P) ≫ f) :=
  kernel.lift_ι (torusUnit Q) _ _

private theorem reducedTensorHomEquiv_symm_π (P Q : PresheafWithTransfers.{u + 1} k)
    (g : P ⟶ contractionKernel Q) :
    cokernel.π ((torusParameterTensorUnit k).app P) ≫ (reducedTensorHomEquiv k P Q).symm g =
      ((a₁).homEquiv P Q).symm (g ≫ kernel.ι (torusUnit Q)) :=
  cokernel.π_desc ((torusParameterTensorUnit k).app P) _ _

/-- The reduced tensor is left adjoint to the literal unit kernel. -/
@[no_expose]
def reducedParameterTensorAdjunction :
    reducedParameterTensorFunctor k ⊣
      (contractionKernelFunctor : PresheafWithTransfers.{u + 1} k ⥤ _) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := reducedTensorHomEquiv k
      homEquiv_naturality_left_symm := by
        intro P' P Q f g
        let i := (torusParameterTensorUnit k).app P'
        let g' : P ⟶ contractionKernel Q := g
        apply (cancel_epi (cokernel.π i)).mp
        change cokernel.π i ≫ (reducedTensorHomEquiv k P' Q).symm (f ≫ g') =
          cokernel.π i ≫ reducedParameterTensorMap k f ≫ (reducedTensorHomEquiv k P Q).symm g'
        rw [reducedTensorHomEquiv_symm_π, reducedParameterTensorMap_π_assoc,
          reducedTensorHomEquiv_symm_π]
        exact (congrArg ((a₁).homEquiv P' Q).symm (Category.assoc f g' _)).trans
          ((a₁).homEquiv_naturality_left_symm f (g' ≫ kernel.ι (torusUnit Q)))
      homEquiv_naturality_right := by
        intro P Q Q' f g
        apply (cancel_mono (kernel.ι (torusUnit Q'))).mp
        change reducedTensorHomEquiv k P Q' (f ≫ g) ≫ kernel.ι (torusUnit Q') =
          (reducedTensorHomEquiv k P Q f ≫ contractionKernelMap g) ≫ kernel.ι (torusUnit Q')
        let p := cokernel.π ((torusParameterTensorUnit k).app P)
        let j := kernel.ι (torusUnit Q)
        let j' := kernel.ι (torusUnit Q')
        let e := reducedTensorHomEquiv k P Q f
        let T : PresheafWithTransfers.{u + 1} k ⥤ PresheafWithTransfers.{u + 1} k :=
          withParameterFunctor Gₘ
        calc
          _ = (a₁).homEquiv P Q' (p ≫ (f ≫ g)) :=
            reducedTensorHomEquiv_ι k P Q' (f ≫ g)
          _ = (a₁).homEquiv P Q' ((p ≫ f) ≫ g) :=
            congrArg ((a₁).homEquiv P Q') (Category.assoc _ _ _).symm
          _ = (a₁).homEquiv P Q (p ≫ f) ≫ T.map g :=
            (a₁).homEquiv_naturality_right (p ≫ f) g
          _ = (e ≫ j) ≫ T.map g :=
            congrArg (· ≫ T.map g) (reducedTensorHomEquiv_ι k P Q f).symm
          _ = e ≫ (j ≫ T.map g) := Category.assoc _ _ _
          _ = e ≫ (contractionKernelMap g ≫ j') :=
            congrArg (e ≫ ·) (contractionKernelMap_ι g).symm
          _ = _ := (Category.assoc _ _ _).symm }

instance : (reducedParameterTensorFunctor k).IsLeftAdjoint :=
  (reducedParameterTensorAdjunction k).isLeftAdjoint

instance : (reducedParameterTensorFunctor k).Additive :=
  (reducedParameterTensorAdjunction k).left_adjoint_additive

/-- The reduced Hom equivalence retains the original quotient and inclusion. -/
@[reassoc]
theorem reducedParameterTensorAdjunction_homEquiv_ι
    {P Q : PresheafWithTransfers.{u + 1} k}
    (f : (reducedParameterTensorFunctor k).obj P ⟶ Q) :
    (reducedParameterTensorAdjunction k).homEquiv P Q f ≫ kernel.ι (torusUnit Q) =
      (a₁).homEquiv P Q ((reducedParameterTensorQuotient k).app P ≫ f) := by
  unfold reducedParameterTensorAdjunction reducedParameterTensorQuotient
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  exact reducedTensorHomEquiv_ι k P Q f

end AlgebraicGeometry.PresheafWithTransfers
