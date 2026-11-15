/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.NisnevichAdjunctionShift
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.AdjunctionShift
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.ReducedTorusComparison
import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.TorusProjectorShift
import StacksFrontier.CategoryTheory.Shift.DetectingCommShift

/-! # The reduced torus transpose after effective reflection -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry.Scheme

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "PST" => LargePresheaves k
local notation "NST" => LargeSheaves k
local notation "E" => EffectiveMotivesMinus k
set_option quotPrecheck false in
local notation "D" => DerivedCategory.Minus PST
set_option quotPrecheck false in
local notation "V" => DerivedCategory.Minus.ι (C := NST)
set_option quotPrecheck false in
local notation "B" => DerivedCategory.Minus.ι (C := PST)
local notation "I" => effectiveMotivesMinusInclusion k
local notation "J" => effectiveMotivesMinusToDerived k
local notation "M" => effectiveReflection k
local notation "R" => effectiveReducedTorusSectionsFunctor k
local notation "T" => reducedTorusSectionsDerivedFunctor k
local notation "U" => forgetDerivedFunctor k
set_option quotPrecheck false in
local notation "A" => (nisnevichSheafify k).mapDerivedCategory
local notation "a" => derivedNisnevichSheafification k
local notation "L" => projectiveReducedTorusTensorToDerivedMinus k
local notation "H" => projectiveEffectiveTorusHomEquiv k
local notation "hᵣ" => projectiveReducedTorusTensorDerivedHomEquiv k

/-- The abelian structure on transfer sheaves for the effective torus shift. -/
local instance torusEffectiveShiftAbelian : Abelian NST := SheafWithTransfers.abelian k

set_option maxHeartbeats 850000 in
-- The two fully faithful inclusions identify the original minus and absolute shifts.
omit [PerfectField k] [HasDerivedCategory AddCommGrpCat.{u + 1}]
  [HasExt (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})] in
private theorem nisnevichTranspose_shifted_map (P : D) (Y : DerivedCategory.Minus NST)
    (f : (a).obj P ⟶ Y) (n : ℤ) :
    (nisnevichDerivedAdjunction k).homEquiv ((B).obj (P⟦n⟧)) ((V).obj (Y⟦n⟧))
        ((V).map (((a).commShiftIso n).hom.app P ≫ f⟦n⟧')) ≫
        (U).map (((V).commShiftIso n).hom.app Y) ≫ ((U).commShiftIso n).hom.app ((V).obj Y) =
      ((B).commShiftIso n).hom.app P ≫
        ((nisnevichDerivedAdjunction k).homEquiv ((B).obj P) ((V).obj Y) ((V).map f))⟦n⟧' := by
  let e : (a) ⋙ V ≅ (B) ⋙ A := Iso.refl _
  let d := nisnevichDerivedAdjunction k
  let : d.CommShift ℤ := nisnevichDerivedAdjunction_commShift k
  let : NatTrans.CommShift e.hom ℤ := nisnevichDerivedMinusInclusion_commShift k
  let δ := ((V).commShiftIso n).hom.app Y
  let p := ((B).commShiftIso n).hom.app P
  let a₀ := (((a) ⋙ V).commShiftIso n).hom.app P
  let a₁ := (((B) ⋙ A).commShiftIso n).hom.app P
  let ψ := d.homEquiv ((B).obj (P⟦n⟧)) (((V).obj Y)⟦n⟧)
  have hshift : a₀ = a₁ := by
    have h := NatTrans.shift_app_comm e.hom n P
    change a₀ ≫ (shiftFunctor (DerivedCategory NST) n).map (𝟙 ((a ⋙ V).obj P)) =
      𝟙 _ ≫ a₁ at h
    rw [(shiftFunctor (DerivedCategory NST) n).map_id ((a ⋙ V).obj P)] at h
    exact (Category.comp_id a₀).symm.trans (h.trans (Category.id_comp a₁))
  let g := (V).map (((a).commShiftIso n).hom.app P ≫ f⟦n⟧')
  let c₀ := ((A).commShiftIso n).hom.app ((B).obj P) ≫ ((V).map f)⟦n⟧'
  have hnat : (V).map (f⟦n⟧') ≫ δ =
      ((V).commShiftIso n).hom.app ((a).obj P) ≫ ((V).map f)⟦n⟧' :=
    ((V).commShiftIso n).hom.naturality f
  have hg : g ≫ δ = (A).map p ≫ c₀ := by
    change (V).map (((a).commShiftIso n).hom.app P ≫ f⟦n⟧') ≫ δ = _
    rw [(V).map_comp, Category.assoc, hnat]
    change (V).map (((a).commShiftIso n).hom.app P) ≫
      ((V).commShiftIso n).hom.app ((a).obj P) ≫ ((V).map f)⟦n⟧' = _
    rw [← Category.assoc]
    have hhead : a₁ = (A).map p ≫ ((A).commShiftIso n).hom.app ((B).obj P) :=
      Functor.commShiftIso_comp_hom_app (B) (A) n P
    have hstart : a₀ = (V).map (((a).commShiftIso n).hom.app P) ≫
        ((V).commShiftIso n).hom.app ((a).obj P) :=
      Functor.commShiftIso_comp_hom_app (a) (V) n P
    exact (congrArg (· ≫ ((V).map f)⟦n⟧') (hstart.symm.trans (hshift.trans hhead))).trans
      (Category.assoc _ _ _)
  let b₀ := ((U).commShiftIso n).hom.app ((V).obj Y)
  let ψ' := d.homEquiv (((B).obj P)⟦n⟧) (((V).obj Y)⟦n⟧)
  have he := d.homEquiv_shift_transport ((V).map f) n
  have hn := d.homEquiv_naturality_left p c₀
  have hq := d.homEquiv_naturality_right g δ
  calc
    _ = ψ (g ≫ δ) ≫ b₀ := (Category.assoc _ _ _).symm.trans (congrArg (· ≫ b₀) hq.symm)
    _ = (p ≫ ψ' c₀) ≫ b₀ := congrArg (· ≫ b₀) ((congrArg ψ hg).trans hn)
    _ = _ := (Category.assoc _ _ _).trans (congrArg (p ≫ ·) he)

set_option maxHeartbeats 1000000 in
-- Each transpose is tested by the actual bounded-above inclusion and derived adjunction.
/-- Compatibility of the reduced derived transpose with shift extends to effective reflection. -/
theorem projectiveEffectiveTorusHomEquiv_shift_of_derived
    (h : ∀ (P : D) (K : DerivedCategory NST) (g : ((L) ⋙ V).obj P ⟶ K) (n : ℤ),
      hᵣ (P⟦n⟧) (K⟦n⟧) ((((L) ⋙ V).commShiftIso n).hom.app P ≫ g⟦n⟧') ≫
          (((T) ⋙ U).commShiftIso n).hom.app K =
        ((B).commShiftIso n).hom.app P ≫ (hᵣ P K g)⟦n⟧')
    (P : D) (K : E) (g : (projectiveEffectiveTorus k).obj P ⟶ K) (n : ℤ) :
    H (P⟦n⟧) (K⟦n⟧)
        (((projectiveEffectiveTorus k).commShiftIso n).hom.app P ≫ g⟦n⟧') ≫
        (((R) ⋙ I).commShiftIso n).hom.app K =
      ((a).commShiftIso n).hom.app P ≫ (H P K g)⟦n⟧' := by
  let adj := effectiveReflectionAdjunction k
  let d := nisnevichDerivedAdjunction k
  let : d.CommShift ℤ := nisnevichDerivedAdjunction_commShift k
  let e := effectiveReducedTorusSectionsToDerivedIso k
  let : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofComp_compatibility e ℤ
  let : NatTrans.CommShift e.inv ℤ := NatTrans.CommShift.of_iso_inv e ℤ
  let g' := ((projectiveEffectiveTorus k).commShiftIso n).hom.app P ≫ g⟦n⟧'
  let f := adj.homEquiv ((L).obj P) K g
  let f' := adj.homEquiv ((L).obj (P⟦n⟧)) (K⟦n⟧) g'
  let ρ := (((R) ⋙ I).commShiftIso n).hom.app K
  let δ := ((V).commShiftIso n).hom.app (((R) ⋙ I).obj K)
  let ε := ((J).commShiftIso n).hom.app K
  let ell := ((a).commShiftIso n).hom.app P
  let v := (V).map f
  let v' := (V).map f'
  let C := (T) ⋙ U
  let Y := (J).obj K
  let Y' := (J).obj (K⟦n⟧)
  let Z := (J).obj ((R).obj K)
  let τ := (U).map (e.inv.app K)
  let τ' := (U).map (e.inv.app (K⟦n⟧))
  let ψ := d.homEquiv ((B).obj (P⟦n⟧)) (Z⟦n⟧)
  let x := H (P⟦n⟧) (K⟦n⟧) g'
  let y := H P K g
  let A₀ := (L).obj P
  let A₁ := (L).obj (P⟦n⟧)
  let l := ((L).commShiftIso n).hom.app P
  let m₀ := ((M).commShiftIso n).hom.app A₀ ≫ g⟦n⟧'
  let i₀ := ((I).commShiftIso n).hom.app K
  have hg' : g' = (M).map l ≫ m₀ := by
    have hu : ((projectiveEffectiveTorus k).commShiftIso n).hom.app P =
        (M).map l ≫ ((M).commShiftIso n).hom.app A₀ :=
      Functor.commShiftIso_comp_hom_app (L) (M) n P
    exact (congrArg (· ≫ g⟦n⟧') hu).trans (Category.assoc _ _ _)
  have hf : f' ≫ i₀ = l ≫ f⟦n⟧' := by
    let α := adj.homEquiv A₁ (K⟦n⟧)
    let β := adj.homEquiv (A₀⟦n⟧) (K⟦n⟧)
    have h₀ : α ((M).map l ≫ m₀) = l ≫ β m₀ := adj.homEquiv_naturality_left l m₀
    have h₁ : β m₀ ≫ i₀ = f⟦n⟧' := adj.homEquiv_shift_transport g n
    exact (congrArg (fun z => α z ≫ i₀) hg').trans
      ((congrArg (· ≫ i₀) h₀).trans ((Category.assoc _ _ _).trans (congrArg (l ≫ ·) h₁)))
  let e₀ := ((V).commShiftIso n).hom.app ((I).obj K)
  have hv : v' ≫ ε = (((L) ⋙ V).commShiftIso n).hom.app P ≫ v⟦n⟧' := by
    have hh : (V).map (f⟦n⟧') ≫ e₀ = ((V).commShiftIso n).hom.app A₀ ≫ v⟦n⟧' :=
      ((V).commShiftIso n).hom.naturality f
    have hε : ε = (V).map i₀ ≫ e₀ := Functor.commShiftIso_comp_hom_app (I) (V) n K
    have hl : (((L) ⋙ V).commShiftIso n).hom.app P =
        (V).map l ≫ ((V).commShiftIso n).hom.app A₀ :=
      Functor.commShiftIso_comp_hom_app (L) (V) n P
    calc
      _ = (V).map f' ≫ (V).map i₀ ≫ e₀ := congrArg (v' ≫ ·) hε
      _ = (V).map l ≫ ((V).commShiftIso n).hom.app A₀ ≫ v⟦n⟧' := by
        rw [← (V).map_comp_assoc, hf, (V).map_comp, Category.assoc, hh]
      _ = _ := (Category.assoc _ _ _).symm.trans (congrArg (· ≫ v⟦n⟧') hl.symm)
  have h₁ : hᵣ (P⟦n⟧) Y' v' ≫ C.map ε ≫ (C.commShiftIso n).hom.app Y =
      ((B).commShiftIso n).hom.app P ≫ (hᵣ P Y v)⟦n⟧' := by
    have he : hᵣ (P⟦n⟧) Y' v' ≫ C.map ε = hᵣ (P⟦n⟧) (Y⟦n⟧) (v' ≫ ε) :=
      (projectiveReducedTorusTensorDerivedHomEquiv_postcompose k (P⟦n⟧) v' ε).symm
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (C.commShiftIso n).hom.app Y)
      (he.trans (congrArg (hᵣ (P⟦n⟧) (Y⟦n⟧)) hv))).trans (h P Y v n))
  let u := ((U).commShiftIso n).hom.app Z
  have h₂ : τ' ≫ (U).map ((V).map ρ) ≫ (U).map δ ≫ u =
      C.map ε ≫ (C.commShiftIso n).hom.app Y ≫ τ⟦n⟧' := by
    have he := NatTrans.shift_app_comm e.inv n K
    change ((J ⋙ T).commShiftIso n).hom.app K ≫ (e.inv.app K)⟦n⟧' =
      e.inv.app (K⟦n⟧) ≫ (((R) ⋙ J).commShiftIso n).hom.app K at he
    have hρ : (V).map ρ ≫ δ = (((R) ⋙ J).commShiftIso n).hom.app K := by
      simp only [ρ, δ, Functor.commShiftIso_comp_hom_app, Functor.map_comp, Category.assoc]
      rfl
    let c₁ := (((J) ⋙ T).commShiftIso n).hom.app K
    let w := (e.inv.app K)⟦n⟧'
    let F := U
    have h₀ : τ' ≫ F.map ((V).map ρ) ≫ F.map δ = F.map (c₁ ≫ w) := by
      calc
        _ = F.map (e.inv.app (K⟦n⟧) ≫ (V).map ρ ≫ δ) := by
          dsimp only [τ']
          rw [F.map_comp, F.map_comp]
        _ = _ := F.congr_map ((congrArg (e.inv.app (K⟦n⟧) ≫ ·) hρ).trans he.symm)
    have hn : F.map w ≫ u = ((F).commShiftIso n).hom.app ((T).obj Y) ≫ τ⟦n⟧' :=
      ((F).commShiftIso n).hom.naturality (e.inv.app K)
    calc
      _ = F.map (c₁ ≫ w) ≫ u := by
        exact (Category.assoc _ _ _).symm.trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (· ≫ u) ((Category.assoc _ _ _).trans h₀))))
      _ = F.map c₁ ≫ ((F).commShiftIso n).hom.app ((T).obj Y) ≫ τ⟦n⟧' := by
        rw [F.map_comp, Category.assoc, hn]
      _ = _ := by
        have hcomp : c₁ = (T).map ε ≫ ((T).commShiftIso n).hom.app Y :=
          Functor.commShiftIso_comp_hom_app (J) (T) n K
        have hc : (C.commShiftIso n).hom.app Y =
            F.map (((T).commShiftIso n).hom.app Y) ≫ ((F).commShiftIso n).hom.app ((T).obj Y) :=
          Functor.commShiftIso_comp_hom_app (T) (F) n Y
        have hm : F.map c₁ = C.map ε ≫ F.map (((T).commShiftIso n).hom.app Y) :=
          (F.congr_map hcomp).trans (F.map_comp _ _)
        exact (congrArg (· ≫ ((F).commShiftIso n).hom.app ((T).obj Y) ≫ τ⟦n⟧') hm).trans
          ((Category.assoc _ _ _).trans
            (congrArg (C.map ε ≫ ·)
              ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ τ⟦n⟧') hc.symm))))
  have hx : d.homEquiv _ _ ((V).map x) = hᵣ (P⟦n⟧) Y' v' ≫ τ' :=
    projectiveEffectiveTorusHomEquiv_map k (P⟦n⟧) (K⟦n⟧) g'
  have hy : d.homEquiv _ _ ((V).map y) = hᵣ P Y v ≫ τ :=
    projectiveEffectiveTorusHomEquiv_map k P K g
  change x ≫ ρ = ell ≫ y⟦n⟧'
  apply (V).map_injective
  apply (cancel_mono δ).mp
  apply ψ.injective
  apply (cancel_mono u).mp
  let X := (B).obj (P⟦n⟧)
  let h₀ := hᵣ (P⟦n⟧) Y' v'
  let t := (V).map ρ ≫ δ
  have hpost : ψ ((V).map (x ≫ ρ) ≫ δ) =
      (d.homEquiv X ((V).obj (((R) ⋙ I).obj (K⟦n⟧))) ((V).map x)) ≫ (U).map t := by
    rw [(V).map_comp, Category.assoc]
    exact d.homEquiv_naturality_right ((V).map x) t
  have hleft : ψ ((V).map (x ≫ ρ) ≫ δ) ≫ u =
      h₀ ≫ τ' ≫ (U).map ((V).map ρ) ≫ (U).map δ ≫ u := by
    calc
      _ = ((h₀ ≫ τ') ≫ (U).map t) ≫ u :=
        (congrArg (· ≫ u) hpost).trans (congrArg (fun q => (q ≫ (U).map t) ≫ u) hx)
      _ = _ := by
        dsimp only [t]
        rw [(U).map_comp]
        simp only [Category.assoc]
  have hright : ψ ((V).map (ell ≫ y⟦n⟧') ≫ δ) ≫ u =
      ((B).commShiftIso n).hom.app P ≫ (hᵣ P Y v ≫ τ)⟦n⟧' := by
    rw [d.homEquiv_naturality_right, Category.assoc]
    exact (nisnevichTranspose_shifted_map k P (((R) ⋙ I).obj K) y n).trans
      (congrArg (((B).commShiftIso n).hom.app P ≫ ·)
        ((shiftFunctor (DerivedCategory PST) n).congr_map hy))
  let z := (τ)⟦n⟧'
  rw [hleft, hright, h₂]
  have ht := congrArg (· ≫ z) h₁
  rw [Functor.map_comp]
  simpa only [Category.assoc] using ht

/-- The actual projective comparison with the effective reduced torus tensor commutes with shift. -/
theorem projectiveEffectiveTorusNatIso_commShift :
    NatTrans.CommShift (projectiveEffectiveTorusNatIso k).hom ℤ :=
  projectiveEffectiveTorusNatIso_commShift_of_homEquiv k
    (projectiveEffectiveTorusHomEquiv_shift_of_derived k
      (projectiveReducedTorusTensorDerivedHomEquiv_shift k))

end AlgebraicGeometry.MotivicHomotopy
