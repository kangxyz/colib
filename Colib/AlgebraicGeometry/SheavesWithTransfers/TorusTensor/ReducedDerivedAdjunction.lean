/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.NisnevichDerived
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived.ReducedFunctor
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.DerivedProjector

/-!
# The reduced derived Hom equivalence

Restrict the original derived Hom equivalence using the two actual
complementary split projections. The result retains the quotient on
the projective tensor and the inclusion of the derived unit kernel.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open AlgebraicGeometry.Scheme

universe u w₁ w₂ w₃

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w₁} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w₂} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w₃} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "PST" => LargePresheaves k
local notation "NST" => LargeSheaves k
local notation "V" => DerivedCategory.Minus.ι (C := NST)
local notation "L" => projectiveTorusTensorToDerivedMinus k ⋙ V
local notation "Lᵣ" => projectiveReducedTorusTensorToDerivedMinus k ⋙ V
local notation "R" => forgetDerivedFunctor k
local notation "T" => torusSectionsDerivedFunctor k
local notation "Tᵣ" => reducedTorusSectionsDerivedFunctor k
local notation "D" => torusTensorDerivedRight k

private abbrev leftQuotient (P : DerivedCategory.Minus PST) :=
  (V).map ((projectiveReducedTorusTensorQuotient k).app P)

private abbrev leftSection (P : DerivedCategory.Minus PST) :=
  (V).map ((projectiveReducedTorusTensorSection k).app P)

private abbrev rightInclusion (K : DerivedCategory NST) :=
  (R).map ((reducedTorusSectionsDerivedInclusion k).app K)

private abbrev rightProjection (K : DerivedCategory NST) :=
  (R).map ((reducedTorusSectionsDerivedProjection k).app K)

private def unrestrictedHomEquiv (P : DerivedCategory.Minus PST) (K : DerivedCategory NST) :
    ((L).obj P ⟶ K) ≃ (P.obj ⟶ (R).obj ((T).obj K)) :=
  (projectiveTorusTensorDerivedHomEquiv k P K).trans
    (Iso.homCongr (Iso.refl _) ((torusSectionsDerivedForgetIso k).app K).symm)

private theorem unrestrictedHomEquiv_post (P : DerivedCategory.Minus PST)
    {K K' : DerivedCategory NST} (f : (L).obj P ⟶ K) (g : K ⟶ K') :
    unrestrictedHomEquiv k P K' (f ≫ g) =
      unrestrictedHomEquiv k P K f ≫ (R).map ((T).map g) := by
  let e := (torusSectionsDerivedForgetIso k).inv
  unfold unrestrictedHomEquiv
  simp only [Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_inv, Category.id_comp,
    Iso.symm_hom, projectiveTorusTensorDerivedHomEquiv_postcompose, Category.assoc]
  exact congrArg (projectiveTorusTensorDerivedHomEquiv k P K f ≫ ·) (e.naturality g)

private theorem unrestrictedHomEquiv_pre {P P' : DerivedCategory.Minus PST}
    (K : DerivedCategory NST) (f : P' ⟶ P) (g : (L).obj P ⟶ K) :
    unrestrictedHomEquiv k P' K ((L).map f ≫ g) =
      f.hom ≫ unrestrictedHomEquiv k P K g := by
  unfold unrestrictedHomEquiv
  simp only [Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_inv, Category.id_comp,
    projectiveTorusTensorDerivedHomEquiv_precompose, Category.assoc]

private theorem unrestrictedHomEquiv_left_right_complement (P : DerivedCategory.Minus PST)
    (K : DerivedCategory NST) (f : (L).obj P ⟶ K) :
    unrestrictedHomEquiv k P K (leftQuotient k P ≫ leftSection k P ≫ f) =
      unrestrictedHomEquiv k P K f ≫ rightProjection k K ≫ rightInclusion k K := by
  let e := (torusSectionsDerivedForgetIso k).app K
  let H := projectiveTorusTensorDerivedHomEquiv k P K
  let q := leftQuotient k P
  let s := leftSection k P
  let r := rightProjection k K
  let i := rightInclusion k K
  let u := (torusSectionsDerivedUnitRestriction k).app K
  let v := (torusSectionsDerivedConstant k).app K
  let u' := (torusPresheafDerivedUnitRestriction k).app ((R).obj K)
  let v' := (torusPresheafDerivedConstant k).app ((R).obj K)
  let b := (projectiveTorusBaseProjector k).app P
  let L₀ := (L).obj P
  let j₀ : L₀ ⟶ L₀ := 𝟙 L₀
  have hq : q ≫ s = j₀ - b := by
    have h := congrArg (V).map (projectiveReducedTorusTensorQuotient_section k P)
    let X := (projectiveTorusTensorToDerivedMinus k).obj P
    let b₀ : X ⟶ X := (Functor.whiskerRight
      (projectiveCoefficientNatTrans k
        (torusParameterTensorProjection k ≫ torusParameterTensorUnit k))
      (nisnevichSheafify k).mapDerivedCategoryMinus).app P
    let iX : X ⟶ X := 𝟙 X
    let jX : L₀ ⟶ L₀ := (V).map iX
    have hi : jX = j₀ := (V).map_id X
    change (V).map (_ ≫ _) = (V).map (iX - b₀) at h
    rw [(V).map_comp, (V).map_sub] at h
    change q ≫ s = jX - b at h
    exact h.trans (congrArg (· - b) hi)
  have hri : r ≫ i = 𝟙 _ - (R).map u ≫ (R).map v := by
    have h := congrArg (R).map (reducedTorusSectionsDerivedProjection_inclusion k K)
    rw [(R).map_comp, (R).map_sub, (R).map_id, (R).map_comp] at h
    exact h
  have hu : e.hom ≫ u' = (R).map u :=
    torusSectionsDerivedForgetIso_hom_app_unitRestriction k K
  have hv : (R).map v ≫ e.hom = v' :=
    torusSectionsDerivedForgetIso_hom_app_constant k K
  have hc : e.inv ≫ (R).map u ≫ (R).map v = u' ≫ v' ≫ e.inv := by
    have he : e.inv ≫ (R).map u = u' := by rw [← hu, e.inv_hom_id_assoc]
    have hd : (R).map v = v' ≫ e.inv :=
      ((Category.assoc _ _ _).trans
        ((congrArg ((R).map v ≫ ·) e.hom_inv_id).trans (Category.comp_id _))).symm.trans
          (congrArg (· ≫ e.inv) hv)
    exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ (R).map v) he)).trans
      (congrArg (u' ≫ ·) hd)
  let h₀ := H f
  let G := unrestrictedHomEquiv k P K
  have hG (x : (L).obj P ⟶ K) : G x = H x ≫ e.inv := by
    unfold G unrestrictedHomEquiv
    simp only [Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_inv, Category.id_comp, Iso.symm_hom]
    rfl
  have hs : q ≫ s ≫ f = f - b ≫ f := by
    calc
      _ = (j₀ - b) ≫ f :=
        (Category.assoc _ _ _).symm.trans (congrArg (· ≫ f) hq)
      _ = _ := (Preadditive.sub_comp _ _ _).trans
        (congrArg (· - b ≫ f) (Category.id_comp f))
  have hb : H (b ≫ f) = h₀ ≫ u' ≫ v' :=
    projectiveTorusTensorDerivedHomEquiv_baseProjector k P K f
  let c₀ : P.obj ⟶ (D).obj K := h₀ ≫ u' ≫ v'
  have hm : H (q ≫ s ≫ f) = h₀ - c₀ :=
    (congrArg H hs).trans ((projectiveTorusTensorDerivedHomEquiv_sub k P K _ _).trans
      (congrArg (h₀ - ·) hb))
  let X := (R).obj ((T).obj K)
  let x : P.obj ⟶ X := h₀ ≫ e.inv
  let y : P.obj ⟶ X := c₀ ≫ e.inv
  let z : P.obj ⟶ X := x ≫ (R).map u ≫ (R).map v
  let v₀ : X ⟶ X := (R).map u ≫ (R).map v
  let i₀ : X ⟶ X := 𝟙 X
  have hf : y = z := by
    calc
      _ = h₀ ≫ u' ≫ v' ≫ e.inv := by
        change (h₀ ≫ u' ≫ v') ≫ e.inv = _
        exact (Category.assoc _ _ _).trans (congrArg (h₀ ≫ ·) (Category.assoc _ _ _))
      _ = h₀ ≫ e.inv ≫ (R).map u ≫ (R).map v := congrArg (h₀ ≫ ·) hc.symm
      _ = _ := (Category.assoc _ _ _).symm
  change G (q ≫ s ≫ f) = G f ≫ r ≫ i
  rw [hG, hG, hm, Preadditive.sub_comp]
  change x - y = x ≫ r ≫ i
  calc
    _ = x - z := congrArg (x - ·) hf
    _ = x ≫ (i₀ - v₀) :=
      (congrArg (· - z) (Category.comp_id x).symm).trans (Preadditive.comp_sub _ _ _).symm
    _ = _ := congrArg (x ≫ ·) hri.symm

/-- The natural derived Hom equivalence of the original reduced projective
torus tensor with derived forget of the actual reduced torus sections. -/
@[no_expose]
def projectiveReducedTorusTensorDerivedHomEquiv
    (P : DerivedCategory.Minus PST) (K : DerivedCategory NST) :
    ((Lᵣ).obj P ⟶ K) ≃ (P.obj ⟶ (R).obj ((Tᵣ).obj K)) where
  toFun f := unrestrictedHomEquiv k P K (leftQuotient k P ≫ f) ≫ rightProjection k K
  invFun g := leftSection k P ≫ (unrestrictedHomEquiv k P K).symm (g ≫ rightInclusion k K)
  left_inv f := by
    have h : leftSection k P ≫ leftQuotient k P = 𝟙 _ := by
      rw [← (V).map_comp, projectiveReducedTorusTensorSection_quotient, (V).map_id]
    have he :
        (unrestrictedHomEquiv k P K (leftQuotient k P ≫ f) ≫ rightProjection k K) ≫
          rightInclusion k K = unrestrictedHomEquiv k P K (leftQuotient k P ≫ f) := by
      rw [Category.assoc, ← unrestrictedHomEquiv_left_right_complement,
        ← Category.assoc (leftSection k P), h, Category.id_comp]
    change leftSection k P ≫ (unrestrictedHomEquiv k P K).symm
      ((unrestrictedHomEquiv k P K (leftQuotient k P ≫ f) ≫ rightProjection k K) ≫
        rightInclusion k K) = f
    rw [he, Equiv.symm_apply_apply, ← Category.assoc, h, Category.id_comp]
  right_inv g := by
    let f := (unrestrictedHomEquiv k P K).symm (g ≫ rightInclusion k K)
    have h : rightInclusion k K ≫ rightProjection k K = 𝟙 _ := by
      rw [← (R).map_comp, reducedTorusSectionsDerivedInclusion_projection, (R).map_id]
    change unrestrictedHomEquiv k P K (leftQuotient k P ≫ leftSection k P ≫ f) ≫
      rightProjection k K = g
    rw [unrestrictedHomEquiv_left_right_complement]
    change (unrestrictedHomEquiv k P K
      ((unrestrictedHomEquiv k P K).symm (g ≫ rightInclusion k K)) ≫
        rightProjection k K ≫ rightInclusion k K) ≫ rightProjection k K = _
    rw [Equiv.apply_symm_apply]
    simp only [Category.assoc, h, Category.comp_id]

/-- The reduced Hom equivalence respects the actual map of the bounded-above source. -/
theorem projectiveReducedTorusTensorDerivedHomEquiv_precompose
    {P P' : DerivedCategory.Minus PST} (K : DerivedCategory NST)
    (f : P' ⟶ P) (g : (Lᵣ).obj P ⟶ K) :
    projectiveReducedTorusTensorDerivedHomEquiv k P' K ((Lᵣ).map f ≫ g) =
      f.hom ≫ projectiveReducedTorusTensorDerivedHomEquiv k P K g := by
  let q := Functor.whiskerRight (projectiveReducedTorusTensorQuotient k) V
  have h := (q.naturality_assoc f g).symm
  unfold projectiveReducedTorusTensorDerivedHomEquiv
  change unrestrictedHomEquiv k P' K (q.app P' ≫ (Lᵣ).map f ≫ g) ≫
      rightProjection k K = _
  rw [h, unrestrictedHomEquiv_pre, Category.assoc]
  rfl

/-- The reduced Hom equivalence respects the original derived map on the target. -/
theorem projectiveReducedTorusTensorDerivedHomEquiv_postcompose
    (P : DerivedCategory.Minus PST) {K K' : DerivedCategory NST}
    (f : (Lᵣ).obj P ⟶ K) (g : K ⟶ K') :
    projectiveReducedTorusTensorDerivedHomEquiv k P K' (f ≫ g) =
      projectiveReducedTorusTensorDerivedHomEquiv k P K f ≫ (R).map ((Tᵣ).map g) := by
  let q := leftQuotient k P
  let ρ := reducedTorusSectionsDerivedProjection k
  have h := congrArg (R).map (ρ.naturality g)
  change (R).map ((T).map g ≫ ρ.app K') = (R).map (ρ.app K ≫ (Tᵣ).map g) at h
  rw [(R).map_comp, (R).map_comp] at h
  unfold projectiveReducedTorusTensorDerivedHomEquiv
  change unrestrictedHomEquiv k P K' (q ≫ f ≫ g) ≫ rightProjection k K' =
    (unrestrictedHomEquiv k P K (q ≫ f) ≫ rightProjection k K) ≫ (R).map ((Tᵣ).map g)
  rw [← Category.assoc q, unrestrictedHomEquiv_post]
  simp only [Category.assoc]
  change unrestrictedHomEquiv k P K (q ≫ f) ≫ (R).map ((T).map g) ≫ (R).map (ρ.app K') =
    unrestrictedHomEquiv k P K (q ≫ f) ≫ (R).map (ρ.app K) ≫ (R).map ((Tᵣ).map g)
  exact congrArg (unrestrictedHomEquiv k P K (q ≫ f) ≫ ·) h

/-- The derived reduced transpose retains the literal quotient and kernel inclusion. -/
@[reassoc]
theorem projectiveReducedTorusTensorDerivedHomEquiv_inclusion
    (P : DerivedCategory.Minus PST) (K : DerivedCategory NST) (f : (Lᵣ).obj P ⟶ K) :
    projectiveReducedTorusTensorDerivedHomEquiv k P K f ≫
      (R).map ((reducedTorusSectionsDerivedInclusion k).app K) ≫
      (torusSectionsDerivedForgetIso k).hom.app K =
    projectiveTorusTensorDerivedHomEquiv k P K
      ((V).map ((projectiveReducedTorusTensorQuotient k).app P) ≫ f) := by
  let q := leftQuotient k P
  let s := leftSection k P
  let e := (torusSectionsDerivedForgetIso k).app K
  have h : s ≫ q = 𝟙 _ := by
    rw [← (V).map_comp, projectiveReducedTorusTensorSection_quotient, (V).map_id]
  unfold projectiveReducedTorusTensorDerivedHomEquiv
  change (unrestrictedHomEquiv k P K (q ≫ f) ≫ rightProjection k K) ≫
    rightInclusion k K ≫ e.hom = _
  let G := unrestrictedHomEquiv k P K
  let r := rightProjection k K
  let i := rightInclusion k K
  have he : G (q ≫ f) ≫ r ≫ i = G (q ≫ f) := by
    have hcomp : s ≫ q ≫ f = f :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ f) h).trans (Category.id_comp f))
    exact (unrestrictedHomEquiv_left_right_complement k P K (q ≫ f)).symm.trans
      (congrArg (fun z => G (q ≫ z)) hcomp)
  have hG : G (q ≫ f) = projectiveTorusTensorDerivedHomEquiv k P K (q ≫ f) ≫ e.inv := by
    unfold G unrestrictedHomEquiv
    simp only [Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_inv, Category.id_comp, Iso.symm_hom]
    rfl
  change (G (q ≫ f) ≫ r) ≫ i ≫ e.hom = projectiveTorusTensorDerivedHomEquiv k P K (q ≫ f)
  calc
    _ = (G (q ≫ f) ≫ r ≫ i) ≫ e.hom := by simp only [Category.assoc]
    _ = G (q ≫ f) ≫ e.hom := congrArg (· ≫ e.hom) he
    _ = _ := (congrArg (· ≫ e.hom) hG).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (projectiveTorusTensorDerivedHomEquiv k P K (q ≫ f) ≫ ·) e.inv_hom_id).trans
          (Category.comp_id _)))

end AlgebraicGeometry.SheafWithTransfers
