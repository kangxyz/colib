/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.NisnevichDerived
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.DerivedForgetComparison
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.ReducedProjectiveRepresentable
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSheafification.DerivedComparison.CancellationRepresentable
import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.NisnevichDerivedUnit
import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.DerivedReindexing
import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.RepresentableCochainTranspose

/-!
# The derived transpose on a single representable

The projective Hom equivalence on a smooth representable is computed on
its original degree-zero complex. The canonical derived-forget comparison
identifies the transpose of the target augmentation with the augmentation
followed by the original singular cancellation map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open AlgebraicGeometry.Scheme

universe u w₁ w₂ w₃

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers MotivicHomotopy

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w₁} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w₂} (SheafWithTransfers.{u + 1} k)]

local notation "PST" => LargePresheaves k
local notation "NST" => LargeSheaves k
local notation "c" => ComplexShape.up ℤ
local notation "S" => Spec (CommRingCat.of k)
local notation "Gₘ" => SmoothSite.multiplicativeGroupObject S
local notation "A" => nisnevichSheafify k
local notation "U" => (SheafWithTransfers.forget k : NST ⥤ PST)
local notation "T" => (withParameterFunctor Gₘ : PST ⥤ PST)
local notation "L" => parameterTensorFunctor Gₘ ⋙ A
local notation "R" => U ⋙ T
local notation "B" => torusSectionsFunctor k
local notation "F" => forgetDerivedFunctor k
local notation "Qₚ" => DerivedCategory.Q (C := PST)
local notation "Qₛ" => DerivedCategory.Q (C := NST)
local notation "sₚ" => CochainComplex.singleFunctor PST 0

private theorem projectiveTorusRepresentableTranspose_injective
    (Y : Cor k) (I : CochainComplex NST ℤ) [hI : I.IsKInjective]
    (g : ((L).mapHomologicalComplex c).obj ((sₚ).obj ((representableLarge k).obj Y)) ⟶ I) :
    projectiveTorusTensorDerivedHomEquiv k (singleTransferRepresentable k Y) ((Qₛ).obj I)
        ((projectiveTorusRepresentableSingleModelIso k Y).hom ≫ (Qₛ).map g) =
      (Qₚ).map ((torusTensorCochainAdjunction k).homEquiv _ I g) ≫
        (T).mapDerivedCategoryFactors.inv.app (((U).mapHomologicalComplex c).obj I) ≫
        (T).mapDerivedCategory.map ((forgetDerivedUnit k).app I) := by
  let J : TorusTensorInjectiveHomotopy k := ⟨(HomotopyCategory.quotient NST c).obj I, hI⟩
  let P := projectiveRepresentableSingle k Y
  let X := singleTransferRepresentable k Y
  let K := (sₚ).obj ((representableLarge k).obj Y)
  let I' := (torusTensorInjectiveToDerived k).obj J
  let j := (DerivedCategory.quotientCompQhIso NST).app I
  let e := projectiveSingleRepresentativeIso k Y
  let l := projectiveTensorModelIso k
  let a := projectiveTorusRepresentableSingleModelIso k Y
  let d := (DerivedCategory.Minus.ι (C := PST)).mapIso
    ((boundedAboveProjectiveEquivalence k).counitIso.app X)
  let p := (DerivedCategory.quotientCompQhIso PST).app K
  let q := (DerivedCategory.quotientCompQhIso PST).app (((R).mapHomologicalComplex c).obj I)
  let Q := DerivedCategory.Qh (C := NST)
  let b := (HomotopyCategory.quotient NST c).map g
  let f := (torusTensorCochainAdjunction k).homEquiv K I g
  let r := (HomotopyCategory.quotient PST c).map f
  let E := torusTensorDerivedRight k
  let Q' := DerivedCategory.Qh (C := PST)
  let v := (DerivedCategory.quotientCompQhIso NST).app (((L).mapHomologicalComplex c).obj K)
  let m := ((L).mapHomotopyCategory c).map e.hom.hom
  let E₀ := (boundedAboveProjectiveEquivalence k).inverse.obj X
  let t := (torusTensorInjectiveReindexingIso k).hom.app J
  have hleft : l.inv.app ((boundedAboveProjectiveEquivalence k).inverse.obj X) ≫
      a.hom ≫ (Qₛ).map g ≫ j.inv =
        Q.map m ≫ Q.map b := by
    have ha : a.hom = (projectiveTensorModel k).map e.hom ≫ l.hom.app P ≫ v.hom :=
      projectiveTorusRepresentableSingleModelIso_hom k Y
    have hn : l.inv.app E₀ ≫ (projectiveTensorModel k).map e.hom = Q.map m ≫ l.inv.app P :=
      (l.inv.naturality e.hom).symm
    have hg : v.hom ≫ (Qₛ).map g = Q.map b ≫ j.hom :=
      (DerivedCategory.quotientCompQhIso_hom_naturality g).symm
    calc
      _ = (l.inv.app E₀ ≫ (projectiveTensorModel k).map e.hom) ≫
          l.hom.app P ≫ v.hom ≫ (Qₛ).map g ≫ j.inv := by
        rw [ha]
        simp only [Category.assoc]
        rfl
      _ = Q.map m ≫ v.hom ≫ (Qₛ).map g ≫ j.inv := by
        rw [hn, Category.assoc, Iso.inv_hom_id_app_assoc]
      _ = Q.map m ≫ (Q.map b ≫ j.hom) ≫ j.inv := by
        exact congrArg (Q.map m ≫ ·) ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ j.inv) hg))
      _ = _ := (congrArg (Q.map m ≫ ·) (Category.assoc _ _ _)).trans
        ((congrArg (Q.map m ≫ Q.map b ≫ ·) j.hom_inv_id).trans
          (congrArg (Q.map m ≫ ·) (Category.comp_id (Q.map b))))
  have hd : d.inv ≫ Q'.map e.hom.hom = p.inv := by
    let Z := (DerivedCategory.Minus.ι (C := PST)).obj X
    let u : (Z ⟶ Q'.obj P.obj) ≃ (Z ⟶ (Qₚ).obj K) := p.homToEquiv
    apply u.injective
    change (d.inv ≫ Q'.map e.hom.hom) ≫ p.hom = p.inv ≫ p.hom
    have h : Q'.map e.hom.hom ≫ p.hom = d.hom := projectiveSingleRepresentativeIso_hom k Y
    exact (Category.assoc _ _ _).trans
      ((congrArg (d.inv ≫ ·) h).trans (d.inv_hom_id.trans p.inv_hom_id.symm))
  have hr : p.inv ≫ Q'.map r = (Qₚ).map f ≫ q.inv :=
    (DerivedCategory.quotientCompQhIso_inv_naturality f).symm
  have hcomp : ((a.hom ≫ (Qₛ).map g) ≫ j.inv) ≫ j.hom = a.hom ≫ (Qₛ).map g :=
    (Category.assoc _ _ _).trans
      ((congrArg ((a.hom ≫ (Qₛ).map g) ≫ ·) j.inv_hom_id).trans (Category.comp_id _))
  have hm : l.inv.app E₀ ≫ ((a.hom ≫ (Qₛ).map g) ≫ j.inv) = Q.map m ≫ Q.map b := by
    simp only [Category.assoc]
    exact hleft
  have hT : q.inv ≫ t ≫ E.map j.hom =
      (T).mapDerivedCategoryFactors.inv.app (((U).mapHomologicalComplex c).obj I) ≫
        (T).mapDerivedCategory.map ((forgetDerivedUnit k).app I) :=
    torusTensorInjectiveReindexingIso_hom_app_quotient k I
  change projectiveTorusTensorDerivedHomEquiv k X ((Qₛ).obj I) (a.hom ≫ (Qₛ).map g) =
    (Qₚ).map f ≫ _
  calc
    _ = projectiveTorusTensorDerivedHomEquiv k X I' ((a.hom ≫ (Qₛ).map g) ≫ j.inv) ≫
        E.map j.hom := by
      exact (congrArg (projectiveTorusTensorDerivedHomEquiv k X ((Qₛ).obj I)) hcomp.symm).trans
        (projectiveTorusTensorDerivedHomEquiv_postcompose k X _ j.hom)
    _ = (d.inv ≫ DerivedCategory.Qh.map e.hom.hom ≫
        DerivedCategory.Qh.map r ≫ (torusTensorInjectiveReindexingIso k).hom.app J) ≫
        E.map j.hom := by
      have hh := projectiveTorusTensorDerivedHomEquiv_on_representatives k X J
        ((a.hom ≫ (Qₛ).map g) ≫ j.inv)
      change projectiveTorusTensorDerivedHomEquiv k X I' ((a.hom ≫ (Qₛ).map g) ≫ j.inv) =
        d.inv ≫ torusTensorHomEquivOnRepresentatives k E₀ J
          (l.inv.app E₀ ≫ ((a.hom ≫ (Qₛ).map g) ≫ j.inv)) at hh
      rw [hh, hm, torusTensorHomEquivOnRepresentatives_precompose k J e.hom (Q.map b),
        projectiveTorusTensor_homotopyHomEquiv_map k P I g]
      simp only [Category.assoc]
      rfl
    _ = _ := by
      change (d.inv ≫ Q'.map e.hom.hom ≫ Q'.map r ≫ t) ≫ E.map j.hom =
        (Qₚ).map f ≫ _
      calc
        _ = (((d.inv ≫ Q'.map e.hom.hom) ≫ Q'.map r) ≫ t) ≫ E.map j.hom := by
          simp only [Category.assoc]
        _ = ((p.inv ≫ Q'.map r) ≫ t) ≫ E.map j.hom :=
          congrArg (fun z => ((z ≫ Q'.map r) ≫ t) ≫ E.map j.hom) hd
        _ = (((Qₚ).map f ≫ q.inv) ≫ t) ≫ E.map j.hom :=
          congrArg (fun z => (z ≫ t) ≫ E.map j.hom) hr
        _ = _ := (by
          simp only [Category.assoc]
          exact congrArg ((Qₚ).map f ≫ ·) hT)

/-- The original cochain transpose computes the actual derived projective
Hom equivalence after exact presheaf reindexing. -/
theorem projectiveTorusRepresentableTranspose
    (Y : Cor k) (I : CochainComplex NST ℤ)
    (g : ((L).mapHomologicalComplex c).obj ((sₚ).obj ((representableLarge k).obj Y)) ⟶ I) :
    projectiveTorusTensorDerivedHomEquiv k (singleTransferRepresentable k Y) ((Qₛ).obj I)
        ((projectiveTorusRepresentableSingleModelIso k Y).hom ≫ (Qₛ).map g) =
      (Qₚ).map ((torusTensorCochainAdjunction k).homEquiv _ I g) ≫
        (T).mapDerivedCategoryFactors.inv.app (((U).mapHomologicalComplex c).obj I) ≫
        (T).mapDerivedCategory.map ((forgetDerivedUnit k).app I) := by
  obtain ⟨J, f, hJ, hf⟩ := Stacks.Injectives.exists_kInjective_resolution_of_grothendieck I
  let : J.IsKInjective := hJ
  let : QuasiIso f := hf
  let D := torusTensorDerivedRight k
  let E := (T).mapDerivedCategory
  let t := (T).mapDerivedCategoryFactors
  let η := forgetDerivedUnit k
  let V := (U).mapHomologicalComplex c
  let W := (R).mapHomologicalComplex c
  let H := torusTensorCochainAdjunction k
  let K := (sₚ).obj ((representableLarge k).obj Y)
  let P : DerivedCategory.Minus PST := singleTransferRepresentable k Y
  let z := (projectiveTorusRepresentableSingleModelIso k Y).hom
  let b := (Qₛ).map f
  let d := D.mapIso (asIso b)
  let m := (Qₚ).map (H.homEquiv K I g)
  let q := t.inv.app (V.obj I)
  have hn : η.app I ≫ (F).map b = (Qₚ).map (V.map f) ≫ η.app J := (η.naturality f).symm
  have ht : t.inv.app (V.obj I) ≫ E.map ((Qₚ).map (V.map f)) =
      (Qₚ).map (W.map f) ≫ t.inv.app (V.obj J) :=
    (t.inv.naturality (V.map f)).symm
  let tr : (P.obj ⟶ D.obj ((Qₛ).obj I)) ≃ (P.obj ⟶ D.obj ((Qₛ).obj J)) := d.homToEquiv
  apply tr.injective
  change projectiveTorusTensorDerivedHomEquiv k P ((Qₛ).obj I)
    (z ≫ (Qₛ).map g) ≫ D.map b = (m ≫ q ≫ E.map (η.app I)) ≫ E.map ((F).map b)
  have hm : H.homEquiv K J (g ≫ f) = H.homEquiv K I g ≫ W.map f :=
    H.homEquiv_naturality_right g f
  have h₀ : (z ≫ (Qₛ).map g) ≫ b = z ≫ (Qₛ).map (g ≫ f) :=
    (Category.assoc _ _ _).trans (congrArg (z ≫ ·) ((Qₛ).map_comp _ _).symm)
  have h₁ : E.map (η.app I) ≫ E.map ((F).map b) =
      E.map ((Qₚ).map (V.map f)) ≫ E.map (η.app J) :=
    (E.map_comp _ _).symm.trans ((E.congr_map hn).trans (E.map_comp _ _))
  calc
    _ = projectiveTorusTensorDerivedHomEquiv k P ((Qₛ).obj J) (z ≫ (Qₛ).map (g ≫ f)) :=
      (projectiveTorusTensorDerivedHomEquiv_postcompose k P (z ≫ (Qₛ).map g) b).symm.trans
        (congrArg (projectiveTorusTensorDerivedHomEquiv k P ((Qₛ).obj J)) h₀)
    _ = (Qₚ).map (H.homEquiv K J (g ≫ f)) ≫ t.inv.app (V.obj J) ≫ E.map (η.app J) :=
      projectiveTorusRepresentableTranspose_injective k Y J (g ≫ f)
    _ = m ≫ ((Qₚ).map (W.map f) ≫ t.inv.app (V.obj J)) ≫ E.map (η.app J) := by
      rw [hm, (Qₚ).map_comp]
      simp only [Category.assoc]
      rfl
    _ = _ := by
      rw [← ht]
      simp only [Category.assoc]
      change m ≫ q ≫ (E.map ((Qₚ).map (V.map f)) ≫ E.map (η.app J)) =
        m ≫ q ≫ (E.map (η.app I) ≫ E.map ((F).map b))
      exact congrArg (m ≫ q ≫ ·) h₁.symm

variable [HasDerivedCategory.{w₃} (LargeAb k)]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))) (LargeAb k))]

private theorem torusSectionsDerivedForgetIso_unit_on_cochain
    (I : CochainComplex NST ℤ) :
    (forgetDerivedUnit k).app (((B).mapHomologicalComplex c).obj I) ≫
        (F).map ((torusSectionsDerivedUnit k).app I) ≫
        (torusSectionsDerivedForgetIso k).hom.app ((Qₛ).obj I) =
      (T).mapDerivedCategoryFactors.inv.app (((U).mapHomologicalComplex c).obj I) ≫
        (T).mapDerivedCategory.map ((forgetDerivedUnit k).app I) := by
  let m := (NatIso.mapHomologicalComplex (torusSectionsUnderlyingIso k).symm c).hom.app I
  have hm : (Qₚ).map m = 𝟙 _ := (Qₚ).map_id _
  have h := torusSectionsDerivedForgetIso_hom_app_Q_obj k I
  rw [torusForgetCompositionUnit_app, torusTensorDerivedRightUnit_app] at h
  change (_ ≫ _) ≫ _ = (Qₚ).map m ≫ _ at h
  exact (Category.assoc _ _ _).symm.trans
    (h.trans ((congrArg (· ≫ _) hm).trans (Category.id_comp _)))

/-- The original projective quotient and singular augmentation transpose
to the original source augmentation followed by the cancellation map. -/
theorem projectiveTorusRepresentableCancellationTranspose (Y : Cor k) :
    let P := (representableLarge k).obj Y
    let C := torusCancellationCoefficients k Y
    let K := (Qₛ).obj (singularSheafCochainComplex k C 0)
    let K' := (torusSectionsDerivedFunctor k).obj K
    let f := (Qₛ).map (torusTensorRepresentableTargetAugmentation k Y)
    let e := (A).mapDerivedCategoryFactors.app ((sₚ).obj P)
    let g := (Qₛ).map (((A).mapHomologicalComplex c).map (singularCochainUnitApp P))
    projectiveTorusTensorDerivedHomEquiv k (singleTransferRepresentable k Y) K
      ((projectiveTorusRepresentableSingleModelIso k Y).hom ≫
        (Qₛ).map (torusTensorRepresentableSingleQuotient k Y) ≫ f) =
      ((nisnevichDerivedAdjunction k).homEquiv ((Qₚ).obj ((sₚ).obj P)) K'
        (e.hom ≫ g ≫ cancellationRepresentableDerivedMap k Y)) ≫
        (torusSectionsDerivedForgetIso k).hom.app K := by
  intro P C K K' f e g
  let I := singularSheafCochainComplex k C 0
  let H := ((B).mapHomologicalComplex c).obj I
  let a := (A).mapHomologicalComplex c
  let V := (U).mapHomologicalComplex c
  let E := (T).mapDerivedCategory
  let m := a.map (singularCochainUnitApp P) ≫
    (singularSheafCochainFunctor k 0).map (torusCancellationParameterMap k Y) ≫
      singularSheafCochainTorusSectionsMap k C
  let η := (Adjunction.mapHomologicalComplexAdjunction
    (nisnevichSheafificationAdjunction k) c).unit
  let ρ := forgetDerivedUnit k
  let γ := torusSectionsDerivedUnit k
  let A' := nisnevichDerivedAdjunction k
  let K₀ := (sₚ).obj P
  let b := (torusSectionsDerivedForgetIso k).hom.app K
  let t := (T).mapDerivedCategoryFactors.inv.app (V.obj I)
  have hb : ρ.app H ≫ (F).map (γ.app I) ≫ b = t ≫ E.map (ρ.app I) :=
    torusSectionsDerivedForgetIso_unit_on_cochain k I
  have hg : g ≫ cancellationRepresentableDerivedMap k Y = (Qₛ).map m ≫ γ.app I := by
    rw [cancellationRepresentableDerivedMap_eq_parameterMap, singularSheafDerivedTorusSectionsMap]
    simp only [m, Functor.map_comp, Category.assoc]
    rfl
  have hn : ρ.app (a.obj K₀) ≫ (F).map ((Qₛ).map m) =
      (Qₚ).map (V.map m) ≫ ρ.app H := (ρ.naturality m).symm
  have hl : A'.unit.app ((Qₚ).obj K₀) ≫ (F).map e.hom =
      (Qₚ).map (η.app K₀) ≫ ρ.app (a.obj K₀) :=
    nisnevichDerivedAdjunction_unit_app_Q_obj k K₀
  let x := torusTensorRepresentableSingleQuotient k Y
  let y := torusTensorRepresentableTargetAugmentation k Y
  let d := (projectiveTorusRepresentableSingleModelIso k Y).hom
  let H' := torusTensorCochainAdjunction k
  let P' := singleTransferRepresentable k Y
  have ht : H'.homEquiv K₀ I (x ≫ y) = η.app K₀ ≫ V.map m :=
    torusTensorRepresentableCochainTranspose k Y
  change projectiveTorusTensorDerivedHomEquiv k P' K (d ≫ (Qₛ).map x ≫ (Qₛ).map y) =
    A'.homEquiv ((Qₚ).obj K₀) K' (e.hom ≫ g ≫ cancellationRepresentableDerivedMap k Y) ≫ b
  calc
    _ = projectiveTorusTensorDerivedHomEquiv k P' K (d ≫ (Qₛ).map (x ≫ y)) :=
      congrArg (fun z => projectiveTorusTensorDerivedHomEquiv k P' K (d ≫ z))
        ((Qₛ).map_comp x y).symm
    _ = (Qₚ).map (H'.homEquiv K₀ I (x ≫ y)) ≫ t ≫ E.map (ρ.app I) :=
      projectiveTorusRepresentableTranspose k Y I (x ≫ y)
    _ = ((Qₚ).map (η.app K₀) ≫ (Qₚ).map (V.map m)) ≫ t ≫ E.map (ρ.app I) := by
      rw [ht, (Qₚ).map_comp]
    _ = (((Qₚ).map (η.app K₀) ≫ ρ.app (a.obj K₀)) ≫ (F).map ((Qₛ).map m)) ≫
        (F).map (γ.app I) ≫ b := by
      simp only [Category.assoc, reassoc_of% hn, hb]
    _ = _ := by
      let H := A'.homEquiv ((Qₚ).obj K₀) K'
      have harg : H (e.hom ≫ g ≫ cancellationRepresentableDerivedMap k Y) =
          H (e.hom ≫ (Qₛ).map m ≫ γ.app I) :=
        congrArg (fun z => H (e.hom ≫ z)) hg
      have h := A'.homEquiv_unit ((Qₚ).obj K₀) K'
        (e.hom ≫ (Qₛ).map m ≫ γ.app I)
      rw [(F).map_comp, (F).map_comp] at h
      calc
        _ = ((A'.unit.app ((Qₚ).obj K₀) ≫ (F).map e.hom) ≫ (F).map ((Qₛ).map m)) ≫
            (F).map (γ.app I) ≫ b :=
          congrArg (fun z => (z ≫ (F).map ((Qₛ).map m)) ≫ (F).map (γ.app I) ≫ b) hl.symm
        _ = (A'.unit.app ((Qₚ).obj K₀) ≫ (F).map e.hom ≫
            (F).map ((Qₛ).map m) ≫ (F).map (γ.app I)) ≫ b := by
          simp only [Category.assoc]
        _ = H (e.hom ≫ (Qₛ).map m ≫ γ.app I) ≫ b := congrArg (· ≫ b) h.symm
        _ = _ := congrArg (· ≫ b) harg.symm

end AlgebraicGeometry.SheafWithTransfers
