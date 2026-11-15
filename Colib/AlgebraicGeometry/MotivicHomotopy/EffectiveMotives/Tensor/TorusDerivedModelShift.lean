/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.TorusRepresentativeShift

/-! # Shift of the original derived torus transpose -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]

local notation "PST" => LargePresheaves k
local notation "NST" => LargeSheaves k
local notation "c" => ComplexShape.up ℤ
local notation "Gₘ" => SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k))
local notation "Pmod" => BoundedAboveProjectiveHomotopy k
local notation "Imod" => TorusTensorInjectiveHomotopy k
local notation "U" => DerivedCategory.Minus.ι (C := PST)
local notation "V" => DerivedCategory.Minus.ι (C := NST)
local notation "Qₚ" => DerivedCategory.Qh (C := PST)
local notation "Qₙ" => DerivedCategory.Qh (C := NST)
local notation "J" => torusTensorInjectiveToDerived k
local notation "R" => torusTensorDerivedRight k
local notation "L" => projectiveTorusTensorToDerivedMinus k ⋙ V
local notation "M" => projectiveTensorModel k
local notation "S₀" => projInclusion k ⋙ Qₚ
set_option quotPrecheck false in
local notation "F₀" => (parameterTensorFunctor Gₘ ⋙ nisnevichSheafify k).mapHomotopyCategory c
local notation "M₀" => projInclusion k ⋙ F₀ ⋙ Qₙ
local notation "E" => boundedAboveProjectiveEquivalence k
set_option quotPrecheck false in
local notation "I" => (E).inverse

/-- The native abelian structure on transfer sheaves for the derived torus model. -/
local instance : Abelian NST := SheafWithTransfers.abelian k

private def torusDerivedModelIso : L ≅ I ⋙ M := by
  let a := (nisnevichSheafify k).mapDerivedCategoryMinus
  let F := parameterTensorFunctor Gₘ
  let T := projectiveHomotopyMapToDerivedMinus k F
  let e : projectiveDerivedMinusFunctor k F ≅ I ⋙ T := Iso.refl _
  exact Functor.isoWhiskerRight (Functor.isoWhiskerRight e a) V ≪≫
    Functor.associator (I ⋙ T) a V ≪≫ Functor.associator I T (a ⋙ V)

private def torusDerivedSourceIso : I ⋙ S₀ ≅ U := by
  let F := (E).functor
  let e : F ⋙ U ≅ S₀ := Iso.refl _
  exact Functor.isoWhiskerLeft I e.symm ≪≫ (Functor.associator I F U).symm ≪≫
    Functor.isoWhiskerRight (E).counitIso U ≪≫ (U).leftUnitor

set_option maxHeartbeats 650000 in
-- The same shifts are carried along the projective inverse and forgetting the bound.
private theorem torusDerivedModelIso_commShift :
    NatTrans.CommShift (torusDerivedModelIso k).hom ℤ := by
  let a := (nisnevichSheafify k).mapDerivedCategoryMinus
  let F := parameterTensorFunctor Gₘ
  let T := projectiveHomotopyMapToDerivedMinus k F
  let e : projectiveDerivedMinusFunctor k F ≅ I ⋙ T := Iso.refl _
  let : NatTrans.CommShift e.hom ℤ := projectiveDerivedMinusFunctor_comp_projective_commShift k F
  let t := Functor.whiskerRight e.hom a
  let : NatTrans.CommShift t ℤ := NatTrans.CommShift.whiskerRight e.hom a ℤ
  let q := Functor.whiskerRight t (V)
  let : NatTrans.CommShift q ℤ := NatTrans.CommShift.whiskerRight t (V) ℤ
  let b := (Functor.associator (I ⋙ T) a (V)).hom
  let d := (Functor.associator (I) T (a ⋙ V)).hom
  let : NatTrans.CommShift b ℤ := NatTrans.CommShift.associator a (V) ℤ
  let : NatTrans.CommShift d ℤ := NatTrans.CommShift.associator T (a ⋙ V) ℤ
  let : NatTrans.CommShift (b ≫ d) ℤ := NatTrans.CommShift.comp b d ℤ
  change NatTrans.CommShift (q ≫ b ≫ d) ℤ
  exact NatTrans.CommShift.comp q (b ≫ d) ℤ

set_option maxHeartbeats 650000 in
-- The counit commutes with the original inclusion of the bounded derived category.
omit [HasDerivedCategory (SheafWithTransfers.{u + 1} k)] in
private theorem torusDerivedSourceIso_commShift :
    NatTrans.CommShift (torusDerivedSourceIso k).hom ℤ := by
  let F := (E).functor
  let e : F ⋙ U ≅ S₀ := Iso.refl _
  let : NatTrans.CommShift e.hom ℤ := boundedAboveProjectiveEquivalence_comp_ι_commShift k
  let : NatTrans.CommShift e.inv ℤ := NatTrans.CommShift.of_iso_inv e ℤ
  let q := Functor.whiskerLeft (I) e.inv
  let b := (Functor.associator (I) F (U)).inv
  let a := Functor.whiskerRight (E).counitIso.hom (U)
  let d := (U).leftUnitor.hom
  let : NatTrans.CommShift q ℤ :=
    inferInstanceAs (NatTrans.CommShift (Functor.whiskerLeft (I) e.inv) ℤ)
  let : NatTrans.CommShift b ℤ := NatTrans.CommShift.of_iso_inv (Functor.associator (I) F (U)) ℤ
  let : NatTrans.CommShift a ℤ := NatTrans.CommShift.whiskerRight (E).counitIso.hom (U) ℤ
  let : NatTrans.CommShift d ℤ := inferInstance
  let : NatTrans.CommShift (a ≫ d) ℤ := NatTrans.CommShift.comp a d ℤ
  let : NatTrans.CommShift (b ≫ a ≫ d) ℤ := NatTrans.CommShift.comp b (a ≫ d) ℤ
  change NatTrans.CommShift (q ≫ b ≫ a ≫ d) ℤ
  exact NatTrans.CommShift.comp q (b ≫ a ≫ d) ℤ

private theorem torusDerivedModelIso_hom_app (P : DerivedCategory.Minus PST) :
    (torusDerivedModelIso k).hom.app P = 𝟙 _ := by
  simp [torusDerivedModelIso]
  rfl

omit [HasDerivedCategory (SheafWithTransfers.{u + 1} k)] in
private theorem torusDerivedSourceIso_inv_app (P : DerivedCategory.Minus PST) :
    (torusDerivedSourceIso k).inv.app P = (U).map ((E).counitIso.inv.app P) := by
  simp [torusDerivedSourceIso, Category.assoc]

set_option maxHeartbeats 850000 in
-- The representative morphism is lifted into the actual K-injective target.
private theorem torusTensorRepresentative_shift (P : Pmod) (K : Imod)
    (f : (M₀).obj P ⟶ (J).obj K) (n : ℤ) :
    torusTensorHomEquivOnRepresentatives k (P⟦n⟧) (K⟦n⟧)
        (((M₀).commShiftIso n).hom.app P ≫ f⟦n⟧' ≫ ((J).commShiftIso n).inv.app K) ≫
        ((J ⋙ R).commShiftIso n).hom.app K =
      ((S₀).commShiftIso n).hom.app P ≫
        (torusTensorHomEquivOnRepresentatives k P K f)⟦n⟧' := by
  let : CochainComplex.IsKInjective K.obj.as := K.property
  let H := F₀
  let Q := Qₙ
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective (H.obj P.obj) K.obj.as).2 f
  let p := ((projInclusion k).commShiftIso n).hom.app P
  let i := ((torusTensorInjectiveInclusion k).commShiftIso n).inv.app K
  let α := (H.commShiftIso n).hom.app P.obj
  let β := (Q.commShiftIso n).hom.app (H.obj P.obj)
  let γ := (Q.commShiftIso n).hom.app K.obj
  let j := ((torusTensorInjectiveInclusion k).commShiftIso n).hom.app K
  let g' := H.map p ≫ α ≫ g⟦n⟧' ≫ i
  have hm : ((M₀).commShiftIso n).hom.app P = Q.map (H.map p) ≫ Q.map α ≫ β := by
    simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_map]
    rfl
  have hj : ((J).commShiftIso n).hom.app K = Q.map j ≫ γ :=
    Functor.commShiftIso_comp_hom_app (torusTensorInjectiveInclusion k) Q n K
  have hg' : Q.map g' ≫ ((J).commShiftIso n).hom.app K =
      ((M₀).commShiftIso n).hom.app P ≫ f⟦n⟧' := by
    rw [hj, hm, ← hg]
    have hn : Q.map (g⟦n⟧') ≫ γ = β ≫ (Q.map g)⟦n⟧' :=
      (Q.commShiftIso n).hom.naturality g
    have hij : Q.map i ≫ Q.map j = 𝟙 _ :=
      (Q.map_comp i j).symm.trans
        ((Q.congr_map (Iso.inv_hom_id_app _ _)).trans (Q.map_id _))
    dsimp only [g']
    simp only [Q.map_comp, Category.assoc, reassoc_of% hij, hn]
    rfl
  have harg : ((M₀).commShiftIso n).hom.app P ≫ f⟦n⟧' ≫ ((J).commShiftIso n).inv.app K =
      Q.map g' := by
    rw [← Category.assoc, ← hg', Category.assoc, Iso.hom_inv_id_app]
    exact Category.comp_id _
  rw [harg, ← hg]
  exact torusTensorHomEquivOnRepresentatives_shift_map k P K g n

set_option maxHeartbeats 950000 in
-- The original projective and injective representatives provide all three comparisons.
private theorem projectiveTorusTensorDerivedHomEquiv_shift_on_injective
    (hModel : NatTrans.CommShift (projectiveTensorModelIso k).hom ℤ)
    (P : DerivedCategory.Minus PST) (K : Imod) (f : (L).obj P ⟶ (J).obj K) (n : ℤ) :
    projectiveTorusTensorDerivedHomEquiv k (P⟦n⟧) (((J).obj K)⟦n⟧)
        (((L).commShiftIso n).hom.app P ≫ f⟦n⟧') ≫ ((R).commShiftIso n).hom.app ((J).obj K) =
      ((U).commShiftIso n).hom.app P ≫
        (projectiveTorusTensorDerivedHomEquiv k P ((J).obj K) f)⟦n⟧' := by
  let X := (I).obj P
  let P' := P⟦n⟧
  let t := ((I).commShiftIso n).hom.app P
  let j := ((J).commShiftIso n).hom.app K
  let i := ((J).commShiftIso n).inv.app K
  let a := ((L).commShiftIso n).hom.app P
  let e := projectiveTensorModelIso k
  let d := torusDerivedSourceIso k
  let l := torusDerivedModelIso k
  let f₀ := e.inv.app X ≫ f
  let f₁ := ((M₀).commShiftIso n).hom.app X ≫ f₀⟦n⟧' ≫ i
  let : NatTrans.CommShift e.hom ℤ := hModel
  let : NatTrans.CommShift e.inv ℤ := NatTrans.CommShift.of_iso_inv e ℤ
  let : NatTrans.CommShift d.hom ℤ := torusDerivedSourceIso_commShift k
  let : NatTrans.CommShift d.inv ℤ := NatTrans.CommShift.of_iso_inv d ℤ
  let : NatTrans.CommShift l.hom ℤ := torusDerivedModelIso_commShift k
  have ha : a = (M).map t ≫ ((M).commShiftIso n).hom.app X := by
    let h : (shiftFunctor (DerivedCategory NST) n).map (𝟙 ((L).obj P)) = 𝟙 _ :=
      (shiftFunctor (DerivedCategory NST) n).map_id _
    have hl := NatTrans.shift_app_comm l.hom n P
    change a ≫ (shiftFunctor (DerivedCategory NST) n).map (l.hom.app P) =
      l.hom.app P' ≫ _ at hl
    rw [torusDerivedModelIso_hom_app k P, torusDerivedModelIso_hom_app k P'] at hl
    have hc : a = ((I ⋙ M).commShiftIso n).hom.app P :=
      (Category.comp_id a).symm.trans ((congrArg (a ≫ ·) h.symm).trans
        (hl.trans (Category.id_comp _)))
    exact hc.trans (Functor.commShiftIso_comp_hom_app (I) (M) n P)
  have he : e.inv.app ((I).obj P') ≫ a ≫ f⟦n⟧' ≫ i = (M₀).map t ≫ f₁ := by
    rw [ha, Category.assoc, ← e.inv.naturality_assoc]
    change (M₀).map t ≫ e.inv.app (X⟦n⟧) ≫ ((M).commShiftIso n).hom.app X ≫ f⟦n⟧' ≫ i = _
    rw [← NatTrans.shift_app_comm_assoc e.inv n X]
    simp only [f₀, f₁, Functor.map_comp, Category.assoc]
  have h₁ : projectiveTorusTensorDerivedHomEquiv k P' (((J).obj K)⟦n⟧) (a ≫ f⟦n⟧') =
      projectiveTorusTensorDerivedHomEquiv k P' ((J).obj (K⟦n⟧)) (a ≫ f⟦n⟧' ≫ i) ≫ (R).map j := by
    have hf : (a ≫ f⟦n⟧' ≫ i) ≫ j = a ≫ f⟦n⟧' := by
      have hij : i ≫ j = 𝟙 _ := Iso.inv_hom_id_app ((J).commShiftIso n) K
      calc
        _ = a ≫ f⟦n⟧' ≫ i ≫ j := by simp only [Category.assoc]
        _ = _ := (congrArg (fun v => a ≫ f⟦n⟧' ≫ v) hij).trans
          (congrArg (a ≫ ·) (Category.comp_id (f⟦n⟧')))
    exact (congrArg (projectiveTorusTensorDerivedHomEquiv k P' (((J).obj K)⟦n⟧)) hf.symm).trans
      (projectiveTorusTensorDerivedHomEquiv_postcompose k P' (a ≫ f⟦n⟧' ≫ i) j)
  have h₂ : projectiveTorusTensorDerivedHomEquiv k P' ((J).obj (K⟦n⟧)) (a ≫ f⟦n⟧' ≫ i) =
      d.inv.app P' ≫ (S₀).map t ≫ torusTensorHomEquivOnRepresentatives k (X⟦n⟧) (K⟦n⟧) f₁ := by
    have h := projectiveTorusTensorDerivedHomEquiv_on_representatives k P' (K⟦n⟧) (a ≫ f⟦n⟧' ≫ i)
    dsimp only [Functor.mapIso_inv, Iso.app_inv] at h
    rw [← torusDerivedSourceIso_inv_app k P'] at h
    exact h.trans ((congrArg (fun z => d.inv.app P' ≫
      torusTensorHomEquivOnRepresentatives k ((I).obj P') (K⟦n⟧) z) he).trans
        (congrArg (d.inv.app P' ≫ ·)
          (torusTensorHomEquivOnRepresentatives_precompose k (K⟦n⟧) t f₁)))
  have h₀ : projectiveTorusTensorDerivedHomEquiv k P ((J).obj K) f =
      d.inv.app P ≫ torusTensorHomEquivOnRepresentatives k X K f₀ := by
    have h := projectiveTorusTensorDerivedHomEquiv_on_representatives k P K f
    dsimp only [Functor.mapIso_inv, Iso.app_inv] at h
    rw [← torusDerivedSourceIso_inv_app k P] at h
    exact h
  have hd : d.inv.app P' ≫ (S₀).map t ≫ ((S₀).commShiftIso n).hom.app X =
      ((U).commShiftIso n).hom.app P ≫ (d.inv.app P)⟦n⟧' := by
    rw [← Functor.commShiftIso_comp_hom_app]
    exact (NatTrans.shift_app_comm d.inv n P).symm
  let g₀ := torusTensorHomEquivOnRepresentatives k X K f₀
  let g₁ := torusTensorHomEquivOnRepresentatives k (X⟦n⟧) (K⟦n⟧) f₁
  let p := d.inv.app P'
  let u := ((U).commShiftIso n).hom.app P
  let b := ((R).commShiftIso n).hom.app ((J).obj K)
  let q := (S₀).map t
  let c₀ := ((S₀).commShiftIso n).hom.app X
  have hcomp : ((J ⋙ R).commShiftIso n).hom.app K = (R).map j ≫ b :=
    Functor.commShiftIso_comp_hom_app (J) (R) n K
  have hs : g₁ ≫ (R).map j ≫ b = c₀ ≫ g₀⟦n⟧' :=
    (congrArg (g₁ ≫ ·) hcomp.symm).trans (torusTensorRepresentative_shift k X K f₀ n)
  rw [h₁, h₂, h₀]
  change ((p ≫ q ≫ g₁) ≫ (R).map j) ≫ b = u ≫ (d.inv.app P ≫ g₀)⟦n⟧'
  calc
    _ = p ≫ q ≫ g₁ ≫ (R).map j ≫ b := by simp only [Category.assoc]
    _ = p ≫ q ≫ c₀ ≫ g₀⟦n⟧' :=
      congrArg (fun x => p ≫ q ≫ x) hs
    _ = (p ≫ q ≫ c₀) ≫ g₀⟦n⟧' := by simp only [Category.assoc]
    _ = (u ≫ (d.inv.app P)⟦n⟧') ≫ g₀⟦n⟧' := congrArg (· ≫ g₀⟦n⟧') hd
    _ = _ := (Category.assoc _ _ _).trans
      (congrArg (u ≫ ·) ((shiftFunctor (DerivedCategory PST) n).map_comp (d.inv.app P) g₀).symm)

set_option maxHeartbeats 650000 in
-- Every target is represented by a K-injective complex, via the actual derived quotient.
/-- The shift compatibility of the projective tensor model passes to the derived transpose. -/
theorem projectiveTorusTensorDerivedHomEquiv_shift_of_model
    (hModel : NatTrans.CommShift (projectiveTensorModelIso k).hom ℤ)
    (P : DerivedCategory.Minus PST) (K : DerivedCategory NST) (f : (L).obj P ⟶ K) (n : ℤ) :
    projectiveTorusTensorDerivedHomEquiv k (P⟦n⟧) (K⟦n⟧)
        (((L).commShiftIso n).hom.app P ≫ f⟦n⟧') ≫ ((R).commShiftIso n).hom.app K =
      ((U).commShiftIso n).hom.app P ≫ (projectiveTorusTensorDerivedHomEquiv k P K f)⟦n⟧' := by
  let I₀ := (J).asEquivalence.inverse.obj K
  let e := (J).asEquivalence.counitIso.app K
  let g := f ≫ e.inv
  let a := ((L).commShiftIso n).hom.app P
  let z := ((R).map e.inv)⟦n⟧'
  have h₁ : projectiveTorusTensorDerivedHomEquiv k (P⟦n⟧) (K⟦n⟧) (a ≫ f⟦n⟧') ≫
          (R).map (e.inv⟦n⟧') =
      projectiveTorusTensorDerivedHomEquiv k (P⟦n⟧) (((J).obj I₀)⟦n⟧) (a ≫ g⟦n⟧') := by
    let sh := shiftFunctor (DerivedCategory NST) n
    have h : (a ≫ f⟦n⟧') ≫ e.inv⟦n⟧' = a ≫ g⟦n⟧' :=
      (Category.assoc _ _ _).trans (congrArg (a ≫ ·) (sh.map_comp f e.inv).symm)
    exact (projectiveTorusTensorDerivedHomEquiv_postcompose k (P⟦n⟧)
      (a ≫ f⟦n⟧') (e.inv⟦n⟧')).symm.trans
        (congrArg (projectiveTorusTensorDerivedHomEquiv k (P⟦n⟧) (((J).obj I₀)⟦n⟧)) h)
  have h₂ : (R).map (e.inv⟦n⟧') ≫ ((R).commShiftIso n).hom.app ((J).obj I₀) =
      ((R).commShiftIso n).hom.app K ≫ z :=
    ((R).commShiftIso n).hom.naturality e.inv
  have h₀ : projectiveTorusTensorDerivedHomEquiv k P ((J).obj I₀) g =
      projectiveTorusTensorDerivedHomEquiv k P K f ≫ (R).map e.inv :=
    projectiveTorusTensorDerivedHomEquiv_postcompose k P f e.inv
  let e' := (shiftFunctor (DerivedCategory PST) n).mapIso ((R).mapIso e.symm)
  let : Mono z := (⟨e'.inv, e'.hom_inv_id⟩ : SplitMono z).mono
  apply (cancel_mono z).mp
  let q := projectiveTorusTensorDerivedHomEquiv k (P⟦n⟧) (K⟦n⟧) (a ≫ f⟦n⟧')
  let q' := projectiveTorusTensorDerivedHomEquiv k (P⟦n⟧) (((J).obj I₀)⟦n⟧) (a ≫ g⟦n⟧')
  let r := projectiveTorusTensorDerivedHomEquiv k P K f
  let r' := projectiveTorusTensorDerivedHomEquiv k P ((J).obj I₀) g
  let b := ((R).commShiftIso n).hom.app K
  let b' := ((R).commShiftIso n).hom.app ((J).obj I₀)
  let u := ((U).commShiftIso n).hom.app P
  let sh := shiftFunctor (DerivedCategory PST) n
  have h : q' ≫ b' = u ≫ sh.map r' :=
    projectiveTorusTensorDerivedHomEquiv_shift_on_injective k hModel P I₀ g n
  change (q ≫ b) ≫ z = (u ≫ sh.map r) ≫ z
  calc
    _ = q ≫ b ≫ z := Category.assoc _ _ _
    _ = q ≫ (R).map (e.inv⟦n⟧') ≫ b' := congrArg (q ≫ ·) h₂.symm
    _ = (q ≫ (R).map (e.inv⟦n⟧')) ≫ b' := (Category.assoc _ _ _).symm
    _ = q' ≫ b' := congrArg (· ≫ b') h₁
    _ = u ≫ sh.map r' := h
    _ = u ≫ sh.map (r ≫ (R).map e.inv) := congrArg (fun v => u ≫ sh.map v) h₀
    _ = _ := (congrArg (u ≫ ·) (sh.map_comp r ((R).map e.inv))).trans (Category.assoc _ _ _).symm

end AlgebraicGeometry.SheafWithTransfers
