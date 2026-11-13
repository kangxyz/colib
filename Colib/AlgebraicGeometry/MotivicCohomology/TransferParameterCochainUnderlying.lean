/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.TransferParameterCochain

/-!
# Forgetting transfers on the placed parameter map

The degreewise ordinary comparison uses the same singular product
and the same sheafification unit. The comparison commutes with
extension by zero in weight-zero cochain placement.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
open Stacks.DerivedIndexing

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Jₖ" => SmoothSite.nisnevichTopology Sₖ
local notation "F" => SheafWithTransfers.toSheaf k
local notation "A" => nisnevichSheafify k
local notation "B" => SheafWithTransfers.torusSectionsFunctor k
local notation "O" => torusParameterSheafFunctor k
local notation "c" => ComplexShape.down ℕ
local notation "d" => ComplexShape.up ℤ
local notation "e" => ComplexShape.embeddingUpIntLE 0
local notation "φ" => SheafWithTransfers.torusSectionsToSheafIso k

private theorem extensionComposite_hom
    {X Y Z : Type*} [Category* X] [Category* Y] [Category* Z]
    [Preadditive X] [Preadditive Y] [Preadditive Z]
    [HasZeroObject X] [HasZeroObject Y] [HasZeroObject Z]
    (G : X ⥤ Y) (H : Y ⥤ Z) [G.Additive] [H.Additive]
    (K : HomologicalComplex X c) :
    (mapExtendIso (G ⋙ H) e K).hom =
      (mapExtendIso H e ((G.mapHomologicalComplex c).obj K)).hom ≫
        (H.mapHomologicalComplex d).map (mapExtendIso G e K).hom := by
  ext i : 1
  change (mapExtendXIso (G ⋙ H) K ((e).r i)).hom =
    (mapExtendXIso H ((G.mapHomologicalComplex c).obj K) ((e).r i)).hom ≫
      H.map (mapExtendXIso G K ((e).r i)).hom
  generalize (e).r i = j
  cases j with
  | none => exact (HomologicalComplex.extend.isZero_X _ rfl).eq_of_src _ _
  | some j =>
    change 𝟙 (H.obj (G.obj (K.X j))) =
      𝟙 (H.obj (G.obj (K.X j))) ≫ H.map (𝟙 (G.obj (K.X j)))
    exact ((congrArg (𝟙 (H.obj (G.obj (K.X j))) ≫ ·) (H.map_id (G.obj (K.X j)))).trans
      (Category.id_comp _)).symm

/-- Forgetting transfers identifies the placed cochains with the original ordinary chains. -/
def ordinarySingularCochainIso (P : PresheafWithTransfers.{u + 1} k) :
    ((F).mapHomologicalComplex d).obj (singularSheafCochainComplex k P 0) ≅
      ((AlgebraicSimplex.sheafifiedSingularChainsFunctor k Jₖ).obj
        ((toPresheaf k).obj P)).extend e :=
  (mapExtendIso (A ⋙ F) e (singularComplex P)).symm ≪≫
    ((e).extendFunctor _).mapIso (singularSheafOrdinaryIso k P)

private theorem ordinarySingularCochainIso_hom (P : PresheafWithTransfers.{u + 1} k) :
    (ordinarySingularCochainIso k P).hom =
      ((F).mapHomologicalComplex d).map (singularSheafCochainExtensionIso k P).inv ≫
        (mapExtendIso (F) e (singularSheafComplex k P)).inv ≫
        ((e).extendFunctor _).map (singularSheafOrdinaryIso k P).hom := by
  let V : SheafWithTransfers.{u + 1} k ⥤ Sheaf Jₖ AddCommGrpCat.{u + 1} := F
  let C := V.mapHomologicalComplex d
  let K := singularComplex P
  let e₁ := mapExtendIso (A) e K
  let e₂ := mapExtendIso V e (singularSheafComplex k P)
  let b := mapExtendIso (A ⋙ V) e K
  let p := ((e).extendFunctor _).map (singularSheafOrdinaryIso k P).hom
  have h : b.hom = e₂.hom ≫ C.map e₁.hom := extensionComposite_hom (A) V K
  have h' : b.inv = C.map e₁.inv ≫ e₂.inv := by
    apply (cancel_mono b.hom).1
    rw [b.inv_hom_id, h, Category.assoc, e₂.inv_hom_id_assoc, ← C.map_comp, e₁.inv_hom_id,
      C.map_id]
    rfl
  change b.inv ≫ p = C.map e₁.inv ≫ e₂.inv ≫ p
  exact (congrArg (· ≫ p) h').trans (Category.assoc _ _ _)

private theorem extensionNaturality
    (K : ChainComplex (SheafWithTransfers.{u + 1} k) ℕ) :
    ((e).extendFunctor _).map
        ((NatTrans.mapHomologicalComplex (φ).hom c).app K) ≫
      (mapExtendIso (F ⋙ O) e K).hom =
    (mapExtendIso (B ⋙ F) e K).hom ≫
      (NatTrans.mapHomologicalComplex (φ).hom d).app (K.extend e) :=
  mapExtendIso_hom_natTrans (φ).hom e K

/-- The original placed transfer map becomes the original ordinary parameter map. -/
theorem ordinarySingularCochainProduct (q : ℕ) :
    let P := reducedTorus k q
    let Q := reducedTorus k (q + 1)
    let C := (F).mapHomologicalComplex d
    let H := (O).mapHomologicalComplex d
    let f := (singularSheafCochainFunctor k 0).map (reducedTorusParameterProduct k q) ≫
      SheafWithTransfers.singularSheafCochainTorusSectionsMap k Q
    let K := singularSheafCochainComplex k Q 0
    let N := (AlgebraicSimplex.sheafifiedSingularChainsFunctor k Jₖ).obj ((toPresheaf k).obj Q)
    let g := ((e).extendFunctor _).map (sheafifiedReducedTorusSingularParameterProduct k q) ≫
      (mapExtendIso (O) e N).hom
    C.map f ≫ (NatTrans.mapHomologicalComplex (φ).hom d).app K ≫
      H.map (ordinarySingularCochainIso k Q).hom =
    (ordinarySingularCochainIso k P).hom ≫ g := by
  intro P Q C H f K N g
  let P₀ := singularSheafComplex k P
  let Q₀ := singularSheafComplex k Q
  let U : SheafWithTransfers.{u + 1} k ⥤ Sheaf Jₖ AddCommGrpCat.{u + 1} := F
  let V : SheafWithTransfers.{u + 1} k ⥤ SheafWithTransfers.{u + 1} k := B
  let R : Sheaf Jₖ AddCommGrpCat.{u + 1} ⥤ Sheaf Jₖ AddCommGrpCat.{u + 1} := O
  let C₀ := U.mapHomologicalComplex c
  let B₀ := V.mapHomologicalComplex c
  let B₁ := V.mapHomologicalComplex d
  let H₀ := R.mapHomologicalComplex c
  let a := transferReducedTorusSingularParameterProduct k q
  let b := sheafifiedReducedTorusSingularParameterProduct k q
  let p := singularSheafCochainExtensionIso k P
  let r := singularSheafCochainExtensionIso k Q
  let z := (mapExtendIso V e Q₀).hom
  let uP := (mapExtendIso U e P₀).hom
  let uQ := (mapExtendIso U e Q₀).hom
  let v := (mapExtendIso U e (B₀.obj Q₀)).hom
  let v' := (mapExtendIso R e (C₀.obj Q₀)).hom
  let o := (mapExtendIso R e N).hom
  let σ : C₀.obj (B₀.obj Q₀) ⟶ H₀.obj (C₀.obj Q₀) :=
    (NatTrans.mapHomologicalComplex (φ).hom c).app Q₀
  let τ : B₁ ⋙ C ⟶ C ⋙ H := NatTrans.mapHomologicalComplex (φ).hom d
  let D := (e).extendFunctor (SheafWithTransfers.{u + 1} k)
  let G := (e).extendFunctor (Sheaf Jₖ AddCommGrpCat.{u + 1})
  let m := (singularSheafOrdinaryIso k P).hom
  let n := (singularSheafOrdinaryIso k Q).hom
  have hf : p.hom ≫ f = D.map a ≫ z ≫ B₁.map r.hom :=
    transferReducedTorusSingularParameterProduct_cochain k q
  have hτ : G.map σ ≫ v' ≫ H.map uQ = v ≫ C.map z ≫ τ.app (Q₀.extend e) := by
    have h := extensionNaturality k Q₀
    have e₁ := extensionComposite_hom V U Q₀
    have e₂ := extensionComposite_hom U R Q₀
    change (mapExtendIso (V ⋙ U) e Q₀).hom = v ≫ C.map z at e₁
    change (mapExtendIso (U ⋙ R) e Q₀).hom = v' ≫ H.map uQ at e₂
    rw [e₁, e₂] at h
    exact h.trans (Category.assoc _ _ _)
  have h₁ : C.map p.hom ≫ C.map f = C.map (D.map a) ≫ C.map z ≫ C.map (B₁.map r.hom) := by
    rw [← C.map_comp, hf, C.map_comp, C.map_comp]
  have h₂ : G.map (C₀.map a) ≫ v = uP ≫ C.map (D.map a) :=
    (mapExtendNatIso U e).hom.naturality a
  have h₃ : G.map (H₀.map n) ≫ o = v' ≫ H.map (G.map n) :=
    (mapExtendNatIso R e).hom.naturality n
  have h₄ : C₀.map a ≫ σ ≫ H₀.map n = m ≫ b :=
    transferReducedTorusSingularParameterProduct_underlying k q
  have h₅ : C.map (B₁.map r.hom) ≫ τ.app K =
      τ.app (Q₀.extend e) ≫ H.map (C.map r.hom) := τ.naturality r.hom
  let uQ' := mapExtendIso U e Q₀
  let uP' := mapExtendIso U e P₀
  have hr : C.map r.hom ≫ (ordinarySingularCochainIso k Q).hom = uQ'.inv ≫ G.map n := by
    rw [ordinarySingularCochainIso_hom, ← C.map_comp_assoc, r.hom_inv_id,
      C.map_id, Category.id_comp]
  have hp : C.map p.hom ≫ (ordinarySingularCochainIso k P).hom = uP'.inv ≫ G.map m := by
    rw [ordinarySingularCochainIso_hom, ← C.map_comp_assoc, p.hom_inv_id,
      C.map_id, Category.id_comp]
  have hτ' : v ≫ C.map z ≫ τ.app (Q₀.extend e) ≫ H.map uQ'.inv = G.map σ ≫ v' := by
    calc
      _ = (v ≫ C.map z ≫ τ.app (Q₀.extend e)) ≫ H.map uQ'.inv := by
        simp only [Category.assoc]
      _ = (G.map σ ≫ v' ≫ H.map uQ) ≫ H.map uQ'.inv :=
        congrArg (· ≫ H.map uQ'.inv) hτ.symm
      _ = G.map σ ≫ v' ≫ H.map (uQ'.hom ≫ uQ'.inv) := by
        change (G.map σ ≫ v' ≫ H.map uQ'.hom) ≫ H.map uQ'.inv = _
        exact (Category.assoc _ _ _).trans ((congrArg (G.map σ ≫ ·)
          (Category.assoc _ _ _)).trans
            (congrArg (fun m => G.map σ ≫ v' ≫ m) (H.map_comp _ _).symm))
      _ = _ := (congrArg (G.map σ ≫ v' ≫ ·)
        ((H.congr_map uQ'.hom_inv_id).trans (H.map_id _))).trans
          ((Category.assoc _ _ _).symm.trans (Category.comp_id _))
  apply (cancel_epi (uP ≫ C.map p.hom)).1
  calc
    _ = uP ≫ C.map (D.map a) ≫ C.map z ≫
        (C.map (B₁.map r.hom) ≫ τ.app K) ≫ H.map (ordinarySingularCochainIso k Q).hom := by
      change (uP ≫ C.map p.hom) ≫ C.map f ≫ τ.app K ≫
        H.map (ordinarySingularCochainIso k Q).hom = _
      simp only [Category.assoc, reassoc_of% h₁]
    _ = uP ≫ C.map (D.map a) ≫ C.map z ≫ τ.app (Q₀.extend e) ≫
        H.map (C.map r.hom ≫ (ordinarySingularCochainIso k Q).hom) := by
      rw [h₅, H.map_comp]
      simp only [Category.assoc]
    _ = G.map (C₀.map a) ≫ G.map σ ≫ v' ≫ H.map (G.map n) := by
      rw [hr, H.map_comp, ← reassoc_of% h₂, reassoc_of% hτ']
    _ = G.map (C₀.map a) ≫ G.map σ ≫ (G.map (H₀.map n) ≫ o) :=
      congrArg (fun m => G.map (C₀.map a) ≫ G.map σ ≫ m) h₃.symm
    _ = G.map (C₀.map a ≫ σ ≫ H₀.map n) ≫ o := by
      simp only [G.map_comp, Category.assoc]
    _ = G.map m ≫ g := by
      change _ = G.map m ≫ (G.map b ≫ o)
      rw [h₄, G.map_comp_assoc]
    _ = uP'.hom ≫ uP'.inv ≫ G.map m ≫ g := (uP'.hom_inv_id_assoc _).symm
    _ = _ := by
      change uP ≫ uP'.inv ≫ G.map m ≫ g =
        (uP ≫ C.map p.hom) ≫ (ordinarySingularCochainIso k P).hom ≫ g
      calc
        _ = uP ≫ (uP'.inv ≫ G.map m) ≫ g := by simp only [Category.assoc]
        _ = uP ≫ (C.map p.hom ≫ (ordinarySingularCochainIso k P).hom) ≫ g :=
          congrArg (fun a => uP ≫ a ≫ g) hp.symm
        _ = _ := by simp only [Category.assoc]

/-- The original signed ordinary shift factors through the placed
ordinary singular comparison. -/
theorem motivicSheafComplexOrdinaryShiftIso_hom_eq (q : ℕ) :
    let C := CochainComplex (Sheaf Jₖ AddCommGrpCat.{u + 1}) ℤ
    let P := reducedTorus k q
    let K := singularSheafCochainComplex k P 0
    let s := -(q : ℤ)
    (motivicSheafComplexOrdinaryShiftIso k q).hom =
      ((F).mapCochainComplexShiftIso s).hom.app K ≫
        (shiftFunctor C s).map (ordinarySingularCochainIso k P).hom := by
  intro C P K s
  unfold motivicSheafComplexOrdinaryShiftIso ordinarySingularCochainIso
  rfl

/-- The inverse comparison uses the same signed placement and original
ordinary singular comparison. -/
theorem motivicSheafComplexOrdinaryShiftIso_inv_eq (q : ℕ) :
    let C := CochainComplex (Sheaf Jₖ AddCommGrpCat.{u + 1}) ℤ
    let P := reducedTorus k q
    let K := singularSheafCochainComplex k P 0
    let s := -(q : ℤ)
    (motivicSheafComplexOrdinaryShiftIso k q).inv =
      (shiftFunctor C s).map (ordinarySingularCochainIso k P).inv ≫
        ((F).mapCochainComplexShiftIso s).inv.app K := by
  intro C P K s
  unfold motivicSheafComplexOrdinaryShiftIso ordinarySingularCochainIso
  rfl

end AlgebraicGeometry.PresheafWithTransfers
