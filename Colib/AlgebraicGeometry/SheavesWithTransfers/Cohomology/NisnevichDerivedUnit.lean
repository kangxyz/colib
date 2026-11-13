/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.NisnevichDerived
import StacksFrontier.Homology.Injectives.DerivedCategory.ArbitraryModelCounit

/-!
# The derived Nisnevich unit on cochain complexes

The unit of the exact derived adjunction retains the termwise sheafification
unit and the original total derived-forget comparison.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open Stacks.DerivedModel

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]

local notation "a" => nisnevichSheafify k
local notation "U" => SheafWithTransfers.forgetDerivedFunctor k
local notation "c" => ComplexShape.up ℤ

private abbrev Qp :
    CochainComplex (PresheafWithTransfers.{u + 1} k) ℤ ⥤
      DerivedCategory (PresheafWithTransfers.{u + 1} k) :=
  DerivedCategory.Q

private abbrev Qs :
    CochainComplex (SheafWithTransfers.{u + 1} k) ℤ ⥤
      DerivedCategory (SheafWithTransfers.{u + 1} k) :=
  DerivedCategory.Q

private theorem homotopyLocalizationQIso_hom_app {A : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] (K : CochainComplex A ℤ) :
    (homotopyLocalizationQIso (A := A)).hom.app
        ((HomotopyCategory.quotient A c).obj K) =
      (homotopyLocalizationQuotientIso DerivedCategory.Q).hom.app K ≫
        (DerivedCategory.quotientCompQhIso A).inv.app K :=
  rfl

private theorem nisnevichDerivedLeftIso_hom_app
    (K : CochainComplex (PresheafWithTransfers.{u + 1} k) ℤ) :
    (nisnevichDerivedLeftIso k).hom.app ((Qp k).obj K) ≫
        (a).mapDerivedCategoryFactors.hom.app K =
      (derivedFunctorOfExact a (Qs k) (Qp k)).map
          ((homotopyLocalizationQuotientIso (Qp k)).inv.app K) ≫
        (derivedFunctorOfExactFac a (Qs k) (Qp k)).hom.app
          ((HomotopyCategory.quotient (PresheafWithTransfers.{u + 1} k) c).obj K) ≫
        (homotopyLocalizationQuotientIso (Qs k)).hom.app
          (((a).mapHomologicalComplex c).obj K) := by
  let P := PresheafWithTransfers.{u + 1} k
  let N := SheafWithTransfers.{u + 1} k
  let Q := DerivedCategory.Qh (C := P)
  let x := (HomotopyCategory.quotient P c).obj K
  let f := (a).mapHomotopyCategory c
  let f₁ := (a).mapHomologicalComplex c
  let A := (a).mapDerivedCategory
  let G := derivedFunctorOfExact a (Qs k) (Qp k)
  let e := nisnevichDerivedLeftIso k
  let d := (DerivedCategory.quotientCompQhIso P).app K
  let d' := (DerivedCategory.quotientCompQhIso N).app (f₁.obj K)
  let p := (homotopyLocalizationQuotientIso (Qp k)).app K
  let n := (homotopyLocalizationQuotientIso (Qs k)).app (f₁.obj K)
  let b := (a).mapDerivedCategoryFactorsh.app x
  let b' := (a).mapDerivedCategoryFactors.app K
  let j := (derivedFunctorOfExactFac a (Qs k) (Qp k)).app x
  have hp : (homotopyLocalizationQIso (A := P)).inv.app x = d.hom ≫ p.inv := by
    let i := (homotopyLocalizationQIso (A := P)).app x
    have hi : i.hom = p.hom ≫ d.inv := homotopyLocalizationQIso_hom_app K
    change i.inv = d.hom ≫ p.inv
    exact (Iso.inv_eq_inv i (p ≪≫ d.symm)).2 hi
  have hn : (homotopyLocalizationQIso (A := N)).hom.app (f.obj x) = n.hom ≫ d'.inv :=
    homotopyLocalizationQIso_hom_app (f₁.obj K)
  have hb : b.hom = A.map d.hom ≫ b'.hom ≫ d'.inv := by
    let Q' := DerivedCategory.Qh (C := N)
    let m := ((a).mapHomotopyCategoryFactors c).inv.app K
    have h : b.hom = A.map d.hom ≫ b'.hom ≫ d'.inv ≫ Q'.map m :=
      (a).mapDerivedCategoryFactorsh_hom_app K
    have hm : Q'.map m = 𝟙 _ := Q'.map_id _
    exact h.trans (congrArg (A.map d.hom ≫ b'.hom ≫ ·)
      ((congrArg (d'.inv ≫ ·) hm).trans (Category.comp_id d'.inv)))
  have he : e.hom.app (Q.obj x) = G.map (d.hom ≫ p.inv) ≫ j.hom ≫
      (n.hom ≫ d'.inv) ≫ b.inv := by
    unfold e nisnevichDerivedLeftIso
    rw [Localization.liftNatIso_hom, Localization.liftNatTrans_app]
    change G.map ((homotopyLocalizationQIso (A := P)).inv.app x) ≫
      (j.hom ≫ (homotopyLocalizationQIso (A := N)).hom.app (f.obj x)) ≫ b.inv = _
    rw [hp, hn]
    exact congrArg (G.map (d.hom ≫ p.inv) ≫ ·) (Category.assoc j.hom (n.hom ≫ d'.inv) b.inv)
  have hb' : b.inv ≫ A.map d.hom ≫ b'.hom = d'.hom := by
    apply (cancel_epi b.hom).1
    rw [b.hom_inv_id_assoc, hb]
    simp only [Category.assoc, d'.inv_hom_id]
    exact congrArg (A.map d.hom ≫ ·) (Category.comp_id b'.hom).symm
  change e.hom.app ((Qp k).obj K) ≫ b'.hom = G.map p.inv ≫ j.hom ≫ n.hom
  apply (cancel_epi (G.map d.hom)).1
  have hnat : G.map d.hom ≫ e.hom.app ((Qp k).obj K) =
      e.hom.app (Q.obj x) ≫ A.map d.hom := e.hom.naturality d.hom
  rw [reassoc_of% hnat, he, G.map_comp]
  simp only [Category.assoc, hb', d'.inv_hom_id, Category.comp_id]

private theorem nisnevichDerivedAdjunctionAux_unit_fac
    (K : HomotopyCategory (PresheafWithTransfers.{u + 1} k) c) :
    (nisnevichDerivedAdjunctionAux k).unit.app ((homotopyLocalization (Qp k)).obj K) ≫
        (U).map ((derivedFunctorOfExactFac a (Qs k) (Qp k)).hom.app K) =
      (homotopyLocalization (Qp k)).map
        ((Adjunction.mapHomotopyCategoryAdjunction (nisnevichSheafificationAdjunction k) c).unit.app
          K) ≫
        (homotopyUnit (SheafWithTransfers.forget k) (Qp k) (Qs k) (U)
          (SheafWithTransfers.forgetDerivedUnit k)).app (((a).mapHomotopyCategory c).obj K) := by
  let F := SheafWithTransfers.forget k
  let G := (a).mapHomotopyCategory c
  let Q := homotopyLocalization (Qs k)
  let Q' := homotopyLocalization (Qp k)
  let L := derivedFunctorOfExact a (Qs k) (Qp k)
  let e := (derivedFunctorOfExactFac a (Qs k) (Qp k)).hom
  let t := homotopyUnit F (Qp k) (Qs k) (U) (SheafWithTransfers.forgetDerivedUnit k)
  let A := Adjunction.mapHomotopyCategoryAdjunction (nisnevichSheafificationAdjunction k) c
  have h : ∃ adj : L ⊣ U,
      (∀ M : HomotopyCategory (PresheafWithTransfers.{u + 1} k) c,
        adj.unit.app (Q'.obj M) ≫ (U).map (e.app M) =
          Q'.map (A.unit.app M) ≫ t.app (G.obj M)) ∧
      (∀ N : HomotopyCategory (SheafWithTransfers.{u + 1} k) c,
        L.map (t.app N) ≫ adj.counit.app (Q.obj N) =
          e.app ((F.mapHomotopyCategory c).obj N) ≫ Q.map (A.counit.app N)) := by
    exact Adjunction.exists_derived_of_isRightDerivedValueAt_of_isLeftDerivedValueAt A
      (HomotopyCategory.quasiIso (SheafWithTransfers.{u + 1} k) c)
      (HomotopyCategory.quasiIso (PresheafWithTransfers.{u + 1} k) c) Q Q' (U) t L e
      (exists_isRightDerivedValueAt_homotopy F (Qs k) (Qp k) (U)
        (SheafWithTransfers.forgetDerivedUnit k))
      (fun M => by
        let H := G ⋙ Q
        let W := HomotopyCategory.quasiIso (PresheafWithTransfers.{u + 1} k) c
        let hInv : W.IsInvertedBy H :=
          isInvertedBy_mapHomotopyCategory_comp_homotopyLocalization a (Qs k)
        refine ⟨Stacks.Injectives.coneOfInvertedMorphisms H W hInv M,
          Stacks.Injectives.coneOfInvertedMorphisms_isLeftDerivedValueAt H W hInv M,
          (derivedFunctorOfExactFac a (Qs k) (Qp k)).app M, fun r => ?_⟩
        have : IsIso (H.map r.hom) := hInv r.hom r.prop
        have h := e.naturality r.hom
        change L.map (Q'.map r.hom) ≫ e.app M ≫ inv (H.map r.hom) = e.app r.left
        have hn : L.map (Q'.map r.hom) ≫ e.app M = e.app r.left ≫ H.map r.hom := h
        calc
          _ = (L.map (Q'.map r.hom) ≫ e.app M) ≫ inv (H.map r.hom) :=
            (Category.assoc _ _ _).symm
          _ = (e.app r.left ≫ H.map r.hom) ≫ inv (H.map r.hom) :=
            congrArg (· ≫ inv (H.map r.hom)) hn
          _ = e.app r.left ≫ (H.map r.hom ≫ inv (H.map r.hom)) :=
            Category.assoc _ _ _
          _ = _ := (congrArg (e.app r.left ≫ ·) (IsIso.hom_inv_id (H.map r.hom))).trans
            (Category.comp_id _))
  change (Classical.choose h).unit.app (Q'.obj K) ≫ (U).map (e.app K) =
    Q'.map (A.unit.app K) ≫ t.app (G.obj K)
  exact (Classical.choose_spec h).1 K

/-- On the original cochain complex, the derived adjunction unit is the
termwise sheafification unit followed by the actual derived-forget unit. -/
@[reassoc]
theorem nisnevichDerivedAdjunction_unit_app_Q_obj
    (K : CochainComplex (PresheafWithTransfers.{u + 1} k) ℤ) :
    (nisnevichDerivedAdjunction k).unit.app (DerivedCategory.Q.obj K) ≫
        (U).map ((a).mapDerivedCategoryFactors.hom.app K) =
      DerivedCategory.Q.map ((Adjunction.mapHomologicalComplexAdjunction
        (nisnevichSheafificationAdjunction k) c).unit.app K) ≫
        (SheafWithTransfers.forgetDerivedUnit k).app (((a).mapHomologicalComplex c).obj K) := by
  let P := PresheafWithTransfers.{u + 1} k
  let N := SheafWithTransfers.{u + 1} k
  let x := (HomotopyCategory.quotient P c).obj K
  let F := SheafWithTransfers.forget k
  let J := ((a).mapHomologicalComplex c).obj K
  let L := homotopyLocalization (Qp k)
  let G := derivedFunctorOfExact a (Qs k) (Qp k)
  let η := (nisnevichDerivedAdjunctionAux k).unit
  let b := (nisnevichDerivedLeftIso k).hom.app ((Qp k).obj K)
  let d := (a).mapDerivedCategoryFactors.hom.app K
  let p := (homotopyLocalizationQuotientIso (Qp k)).app K
  let n := (homotopyLocalizationQuotientIso (Qs k)).app J
  let j := (derivedFunctorOfExactFac a (Qs k) (Qp k)).hom.app x
  let m := ((Adjunction.mapHomologicalComplexAdjunction
    (nisnevichSheafificationAdjunction k) c).unit.app K)
  let α := SheafWithTransfers.forgetDerivedUnit k
  let β := homotopyUnit F (Qp k) (Qs k) (U) α
  have hη : p.hom ≫ η.app ((Qp k).obj K) = η.app (L.obj x) ≫ (U).map (G.map p.hom) :=
    η.naturality p.hom
  have hβ : β.app ((HomotopyCategory.quotient N c).obj J) =
      (homotopyLocalizationQuotientIso (Qp k)).hom.app ((F.mapHomologicalComplex c).obj J) ≫
        α.app J ≫ (U).map n.inv := by
    let T := ((F).mapHomologicalComplex c).obj J
    let q := (DerivedCategory.quotientCompQhIso P).hom.app T
    let Q := DerivedCategory.Qh (C := P)
    let f := (F.mapHomotopyCategoryFactors c).hom.app J
    let u := (Localization.uniq (DerivedCategory.Q (C := P)) (Qp k)
      (HomologicalComplex.quasiIso P c)).functor
    let v := (Localization.compUniqFunctor (DerivedCategory.Q (C := P)) (Qp k)
      (HomologicalComplex.quasiIso P c)).hom.app T
    have h₁ : (mapHomotopyCategoryCompQhIso F).hom.app J = q := by
      change 𝟙 _ ≫ Q.map f ≫ 𝟙 _ ≫ q = q
      have hf : Q.map f = 𝟙 _ := Q.map_id _
      rw [hf]
      all_goals simp only [Category.id_comp]
    have h₂ : (mapHomotopyCategoryCompLocalizationIso F (Qp k)).hom.app J =
        (homotopyLocalizationQuotientIso (Qp k)).hom.app T := by
      change 𝟙 _ ≫ u.map ((mapHomotopyCategoryCompQhIso F).hom.app J) ≫ 𝟙 _ ≫ v =
        𝟙 _ ≫ u.map q ≫ v
      exact (congrArg (fun m => 𝟙 _ ≫ u.map m ≫ 𝟙 _ ≫ v) h₁).trans
        (congrArg (𝟙 _ ≫ u.map q ≫ ·) (Category.id_comp v))
    have h₃ : (homotopyLocalizationCompIso (Qs k) (U)).inv.app J = (U).map n.inv ≫ 𝟙 _ :=
      rfl
    have h := homotopyUnit_app_quotient F (Qp k) (Qs k) (U) α J
    exact h.trans (congrArg₂ (fun l r => l ≫ α.app J ≫ r) h₂
      (h₃.trans (Category.comp_id _)))
  have hm : L.map ((HomotopyCategory.quotient P c).map m) ≫
      (homotopyLocalizationQuotientIso (Qp k)).hom.app ((F.mapHomologicalComplex c).obj J) =
        p.hom ≫ (Qp k).map m := (homotopyLocalizationQuotientIso (Qp k)).hom.naturality m
  have hfac : η.app (L.obj x) ≫ (U).map j =
      L.map ((HomotopyCategory.quotient P c).map m) ≫
        β.app ((HomotopyCategory.quotient N c).obj J) :=
    nisnevichDerivedAdjunctionAux_unit_fac k x
  have hn' : (U).map n.inv ≫ (U).map n.hom = 𝟙 _ := by
    rw [← (U).map_comp, n.inv_hom_id]
    exact (U).map_id _
  have hb : G.map p.hom ≫ (b ≫ d) = j ≫ n.hom := by
    change G.map p.hom ≫
      ((nisnevichDerivedLeftIso k).hom.app ((Qp k).obj K) ≫ d) = j ≫ n.hom
    rw [nisnevichDerivedLeftIso_hom_app k K]
    have h : G.map p.hom ≫ G.map p.inv = 𝟙 _ := by
      rw [← G.map_comp, p.hom_inv_id]
      exact G.map_id _
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ j ≫ n.hom) h).trans (Category.id_comp _))
  change (η.app ((Qp k).obj K) ≫ (U).map b) ≫ (U).map d =
    (Qp k).map m ≫ α.app J
  apply (cancel_epi p.hom).1
  calc
    _ = (p.hom ≫ η.app ((Qp k).obj K)) ≫ (U).map (b ≫ d) := by
      simp only [Category.assoc, (U).map_comp]
    _ = η.app (L.obj x) ≫ (U).map (G.map p.hom ≫ (b ≫ d)) := by
      rw [hη]
      simp only [Category.assoc, (U).map_comp]
    _ = (η.app (L.obj x) ≫ (U).map j) ≫ (U).map n.hom := by
      rw [hb, (U).map_comp]
      exact (Category.assoc _ _ _).symm
    _ = (L.map ((HomotopyCategory.quotient P c).map m) ≫
        β.app ((HomotopyCategory.quotient N c).obj J)) ≫ (U).map n.hom :=
      congrArg (· ≫ (U).map n.hom) hfac
    _ = _ := by
      rw [hβ]
      simp only [Category.assoc, reassoc_of% hm, hn']
      exact congrArg (p.hom ≫ (Qp k).map m ≫ ·) (Category.comp_id (α.app J))

end AlgebraicGeometry.MotivicHomotopy
