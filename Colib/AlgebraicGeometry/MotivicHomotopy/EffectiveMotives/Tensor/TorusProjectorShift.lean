/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.TorusRepresentativeShift
import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.TorusDerivedModelShift
import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.TorusForgetComparisonShift
import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.TorusProjectiveModelShift
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ProjectiveCoefficientMap
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived.ReducedShift
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.ReducedDerivedAdjunction

/-! # The original torus quotient and kernel inclusion preserve shift -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry.Scheme

universe u w w' w''

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]

/-- The literal quotient from the projective torus model to its reduced summand
intertwines the original coefficient shifts. -/
theorem projectiveReducedTorusTensorQuotient_commShift :
    NatTrans.CommShift (projectiveReducedTorusTensorQuotient k) ℤ := by
  let v := reducedParameterTensorQuotient k
  let p := projectiveDerivedMinusFunctorMap v
  let a := (nisnevichSheafify k).mapDerivedCategoryMinus
  have h : p = projectiveCoefficientNatTrans k v := by
    apply NatTrans.ext
    funext K
    let V := DerivedCategory.Minus.ι (C := LargePresheaves k)
    apply V.map_injective
    exact (projectiveDerivedMinusFunctorMap_map_app v K).trans
      (projectiveCoefficientNatTrans_app_hom k v K).symm
  let : NatTrans.CommShift p ℤ := projectiveDerivedMinusFunctorMap_commShift v
  have hp : projectiveReducedTorusTensorQuotient k = Functor.whiskerRight p a :=
    congrArg (fun t => Functor.whiskerRight t a) h.symm
  rw [hp]
  let t := Functor.whiskerRight p a
  let : NatTrans.CommShift t ℤ := NatTrans.CommShift.whiskerRight p a ℤ
  refine ⟨fun n => NatTrans.ext (funext fun K => ?_)⟩
  change ((projectiveTorusTensorToDerivedMinus k).commShiftIso n).hom.app K ≫ (t.app K)⟦n⟧' =
    t.app (K⟦n⟧) ≫ ((projectiveReducedTorusTensorToDerivedMinus k).commShiftIso n).hom.app K
  rw [projectiveTorusTensorToDerivedMinus_commShiftIso_hom_app,
    projectiveReducedTorusTensorToDerivedMinus_commShiftIso_hom_app]
  exact NatTrans.shift_app_comm t n K

variable [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "PST" => LargePresheaves k
local notation "NST" => LargeSheaves k
local notation "U" => DerivedCategory.Minus.ι (C := PST)
local notation "V" => DerivedCategory.Minus.ι (C := NST)
local notation "L" => projectiveTorusTensorToDerivedMinus k ⋙ V
local notation "Lᵣ" => projectiveReducedTorusTensorToDerivedMinus k ⋙ V
local notation "D" => torusTensorDerivedRight k
local notation "Dᵣ" => reducedTorusSectionsDerivedFunctor k ⋙ forgetDerivedFunctor k

set_option maxHeartbeats 650000 in
-- The comparison uses the actual source quotient and the actual target inclusion.
/-- Reducing the torus transpose retains a given shift comparison of the full transpose
when its original target comparison preserves the shift. -/
theorem projectiveReducedTorusTensorDerivedHomEquiv_shift_of_unreduced
    (hForget : NatTrans.CommShift (torusSectionsDerivedForgetIso k).hom ℤ)
    (hFull : ∀ (P : DerivedCategory.Minus PST) (K : DerivedCategory NST)
        (g : (L).obj P ⟶ K) (n : ℤ),
      projectiveTorusTensorDerivedHomEquiv k (P⟦n⟧) (K⟦n⟧)
          (((L).commShiftIso n).hom.app P ≫ g⟦n⟧') ≫ ((D).commShiftIso n).hom.app K =
        ((U).commShiftIso n).hom.app P ≫ (projectiveTorusTensorDerivedHomEquiv k P K g)⟦n⟧')
    (P : DerivedCategory.Minus PST) (K : DerivedCategory NST) (g : (Lᵣ).obj P ⟶ K) (n : ℤ) :
    projectiveReducedTorusTensorDerivedHomEquiv k (P⟦n⟧) (K⟦n⟧)
        (((Lᵣ).commShiftIso n).hom.app P ≫ g⟦n⟧') ≫ ((Dᵣ).commShiftIso n).hom.app K =
      ((U).commShiftIso n).hom.app P ≫
        (projectiveReducedTorusTensorDerivedHomEquiv k P K g)⟦n⟧' := by
  let q := Functor.whiskerRight (projectiveReducedTorusTensorQuotient k) (V)
  let i := Functor.whiskerRight (reducedTorusSectionsDerivedInclusion k) (forgetDerivedFunctor k)
  let e := torusSectionsDerivedForgetIso k
  let j := i ≫ e.hom
  let : NatTrans.CommShift q ℤ := by
    let := projectiveReducedTorusTensorQuotient_commShift k
    exact NatTrans.CommShift.whiskerRight (projectiveReducedTorusTensorQuotient k) (V) ℤ
  let : NatTrans.CommShift i ℤ := by
    let := reducedTorusSectionsDerivedInclusion_commShift k
    exact NatTrans.CommShift.whiskerRight (reducedTorusSectionsDerivedInclusion k)
      (forgetDerivedFunctor k) ℤ
  let := hForget
  let : NatTrans.CommShift j ℤ := NatTrans.CommShift.comp i e.hom ℤ
  let a := ((L).commShiftIso n).hom.app P
  let b := ((Lᵣ).commShiftIso n).hom.app P
  let c₀ := ((U).commShiftIso n).hom.app P
  let d := ((D).commShiftIso n).hom.app K
  let d₀ := ((Dᵣ).commShiftIso n).hom.app K
  let P' := P⟦n⟧
  let K' := K⟦n⟧
  let u := projectiveReducedTorusTensorDerivedHomEquiv k P K g
  let u' := projectiveReducedTorusTensorDerivedHomEquiv k P' K' (b ≫ g⟦n⟧')
  have hq : q.app P' ≫ b = a ≫ (q.app P)⟦n⟧' := (NatTrans.shift_app_comm q n P).symm
  have hj : d₀ ≫ (j.app K)⟦n⟧' = j.app K' ≫ d := NatTrans.shift_app_comm j n K
  have hu : u ≫ j.app K =
      projectiveTorusTensorDerivedHomEquiv k P K (q.app P ≫ g) := by
    exact projectiveReducedTorusTensorDerivedHomEquiv_inclusion k P K g
  have hu' : u' ≫ j.app K' =
      projectiveTorusTensorDerivedHomEquiv k P' K' (q.app P' ≫ b ≫ g⟦n⟧') := by
    exact projectiveReducedTorusTensorDerivedHomEquiv_inclusion k P' K' (b ≫ g⟦n⟧')
  have hm : Mono ((j.app K)⟦n⟧') := by
    let sh := shiftFunctor (DerivedCategory PST) n
    let F := forgetDerivedFunctor k
    let ι := (reducedTorusSectionsDerivedInclusion k).app K
    let r := (reducedTorusSectionsDerivedProjection k).app K
    have hr : ι ≫ r = 𝟙 _ := reducedTorusSectionsDerivedInclusion_projection k K
    let s := ((e.inv.app K) ≫ (forgetDerivedFunctor k).map r)⟦n⟧'
    have hs : (j.app K)⟦n⟧' ≫ s = 𝟙 _ := by
      rw [← Functor.map_comp]
      change (shiftFunctor _ n).map
        (((forgetDerivedFunctor k).map ι ≫ e.hom.app K) ≫
          e.inv.app K ≫ (forgetDerivedFunctor k).map r) = _
      rw [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp, hr]
      exact (congrArg sh.map (F.map_id _)).trans (sh.map_id _)
    exact (SplitMono.mk s hs).mono
  let := hm
  apply (cancel_mono ((j.app K)⟦n⟧')).1
  change (u' ≫ d₀) ≫ (j.app K)⟦n⟧' = (c₀ ≫ u⟦n⟧') ≫ (j.app K)⟦n⟧'
  calc
    _ = (u' ≫ j.app K') ≫ d := by rw [Category.assoc, hj, Category.assoc]
    _ = projectiveTorusTensorDerivedHomEquiv k P' K' (a ≫ (q.app P ≫ g)⟦n⟧') ≫ d := by
      rw [hu', ← Category.assoc (q.app P'), hq, Category.assoc, Functor.map_comp]
    _ = c₀ ≫ (projectiveTorusTensorDerivedHomEquiv k P K (q.app P ≫ g))⟦n⟧' :=
      hFull P K _ n
    _ = _ := by rw [← hu, Functor.map_comp, Category.assoc]

/-- The original reduced torus Hom equivalence intertwines the actual derived shifts. -/
theorem projectiveReducedTorusTensorDerivedHomEquiv_shift
    (P : DerivedCategory.Minus PST) (K : DerivedCategory NST) (g : (Lᵣ).obj P ⟶ K) (n : ℤ) :
    projectiveReducedTorusTensorDerivedHomEquiv k (P⟦n⟧) (K⟦n⟧)
        (((Lᵣ).commShiftIso n).hom.app P ≫ g⟦n⟧') ≫ ((Dᵣ).commShiftIso n).hom.app K =
      ((U).commShiftIso n).hom.app P ≫
        (projectiveReducedTorusTensorDerivedHomEquiv k P K g)⟦n⟧' :=
  projectiveReducedTorusTensorDerivedHomEquiv_shift_of_unreduced k
    (torusSectionsDerivedForgetIso_commShift k)
    (projectiveTorusTensorDerivedHomEquiv_shift_of_model k (projectiveTensorModelIso_commShift k))
    P K g n

end AlgebraicGeometry.SheafWithTransfers
