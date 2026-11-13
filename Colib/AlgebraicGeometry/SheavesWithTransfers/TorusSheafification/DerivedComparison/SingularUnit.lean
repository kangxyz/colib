/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived.UnitSplit
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSheafification.SingularParameterNaturality
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
# Unit compatibility of the original singular comparison

In the base parameter, the signed permutation commutes with the literal
first projection. This identifies the base comparison with the identity
in base-product coordinates. Thus the torus comparison commutes with
restriction to the original unit in the derived category.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme SmoothSite.Contraction
open Stacks.DerivedIndexing

universe w u

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "G" => SmoothSite.multiplicativeGroupObject S
local notation "B" => SmoothSite.base S

private theorem baseSectionsPresheafIso_hom_singular
    (P : PresheafWithTransfers.{u + 1} k) :
    singularComplexMap (baseSectionsPresheafIso k P).hom =
      (((Functor.mapHomologicalComplexIdIso _ (.down ℕ)).inv ≫
        (baseSectionsPresheafNatIso k).hom.mapHomologicalComplex (.down ℕ)).app
          (singularComplex P)) ≫ (withParameterSingularComplexIso P B).hom := by
  ext n : 1
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext V
  let X := V.unop.toSmoothSite
  let Δ := AlgebraicSimplex.smoothSiteObj k n
  let γ := Cor.graphFunctor k
  change transfer P (γ.map (productBaseIso (SmoothSite.product X Δ)).hom) =
    transfer P ((Cor.parameterProduct Δ).map (γ.map (productBaseIso X).hom)) ≫
      transfer P ((Cor.parameterProductSwapNatIso Δ B).hom.app V.unop)
  rw [← transfer_comp, Cor.parameterProduct_graph, Cor.parameterProductSwapNatIso_hom_app,
    ← γ.map_comp]
  exact congrArg (fun f => transfer P (γ.map f)) (by
    change (productBaseIso (SmoothSite.product X Δ)).hom =
      SmoothSite.productSwapLast X Δ B ≫ SmoothSite.productMap (productBaseIso X).hom (𝟙 Δ)
    apply SmoothSite.product_hom_ext
    · simp [productBaseIso, SmoothSite.productSwapLast, Category.assoc]
    · simp [productBaseIso, SmoothSite.productSwapLast_snd, Category.assoc])

private def baseSectionsSheafComplexIso (P : PresheafWithTransfers.{u + 1} k) :
    singularSheafComplex k P ≅
      ((parameterSectionsFunctor k B).mapHomologicalComplex (.down ℕ)).obj
        (singularSheafComplex k P) :=
  (Functor.mapHomologicalComplexIdIso _ (.down ℕ)).symm.app _ ≪≫
    (NatIso.mapHomologicalComplex (baseSectionsSheafIso k) (.down ℕ)).app _

private def baseSectionsSheafCochainIso (P : PresheafWithTransfers.{u + 1} k) :
    singularSheafCochainComplex k P 0 ≅
      ((parameterSectionsFunctor k B).mapHomologicalComplex (.up ℤ)).obj
        (singularSheafCochainComplex k P 0) :=
  (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).symm.app _ ≪≫
    (NatIso.mapHomologicalComplex (baseSectionsSheafIso k) (.up ℤ)).app _

private theorem singularSheafParameterSectionsMap_base
    (P : PresheafWithTransfers.{u + 1} k) :
    (singularSheafFunctor k).map (baseSectionsPresheafIso k P).hom ≫
      singularSheafParameterSectionsMap k B P = (baseSectionsSheafComplexIso k P).hom := by
  let A := (nisnevichSheafify k).mapHomologicalComplex (.down ℕ)
  let b := (((Functor.mapHomologicalComplexIdIso _ (.down ℕ)).inv ≫
    (baseSectionsPresheafNatIso k).hom.mapHomologicalComplex (.down ℕ)).app (singularComplex P))
  let e := withParameterSingularComplexIso P B
  let τ := parameterSectionsSheafificationComplexMap k B (.down ℕ) (singularComplex P)
  have h : A.map (singularComplexMap (baseSectionsPresheafIso k P).hom) ≫ A.map e.inv =
      A.map b := by
    rw [baseSectionsPresheafIso_hom_singular, ← A.map_comp, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  change A.map (singularComplexMap (baseSectionsPresheafIso k P).hom) ≫
    (A.map e.inv ≫ τ) = _
  rw [← Category.assoc, h]
  ext i : 1
  exact baseSectionsSheafification_hom k ((singularComplex P).X i)

private theorem baseSectionsSheafComplexIso_extend
    (P : PresheafWithTransfers.{u + 1} k) :
    let e := ComplexShape.embeddingUpIntLE 0
    let K := singularSheafComplex k P
    let a := mapExtendIso (nisnevichSheafify k) e (singularComplex P)
    let b := mapExtendIso (parameterSectionsFunctor k B) e K
    (e.extendFunctor _).map (baseSectionsSheafComplexIso k P).hom ≫ b.hom ≫
        ((parameterSectionsFunctor k B).mapHomologicalComplex (.up ℤ)).map a.hom =
      a.hom ≫ (baseSectionsSheafCochainIso k P).hom := by
  let e := ComplexShape.embeddingUpIntLE 0
  let K := singularSheafComplex k P
  let L := singularSheafCochainComplex k P 0
  let F := 𝟭 (SheafWithTransfers.{u + 1} k)
  let B₀ := parameterSectionsFunctor k B
  let H := e.extendFunctor (SheafWithTransfers.{u + 1} k)
  let G₁ := B₀.mapHomologicalComplex (.up ℤ)
  let η := (baseSectionsSheafIso k).hom
  let η₀ := η.mapHomologicalComplex (.down ℕ)
  let η₁ := η.mapHomologicalComplex (.up ℤ)
  let u₀ := (Functor.mapHomologicalComplexIdIso (SheafWithTransfers.{u + 1} k) (.down ℕ)).app K
  let u₁ := Functor.mapHomologicalComplexIdIso (SheafWithTransfers.{u + 1} k) (.up ℤ)
  let b := mapExtendIso F e K
  let a := (mapExtendIso (nisnevichSheafify k) e (singularComplex P)).hom
  let g := (mapExtendIso B₀ e K).hom
  have hId : b.hom = H.map u₀.hom ≫ u₁.inv.app (H.obj K) := by
    apply HomologicalComplex.hom_f_injective
    funext i
    change (mapExtendXIso F K (e.r i)).hom =
      HomologicalComplex.extend.mapX u₀.hom (e.r i) ≫ (u₁.inv.app (H.obj K)).f i
    let m := HomologicalComplex.extend.mapX u₀.hom (e.r i)
    have hm : (mapExtendXIso F K (e.r i)).hom = m := by
      dsimp only [m]
      generalize e.r i = j
      cases j with
      | none => exact (HomologicalComplex.extend.isZero_X _ rfl).eq_of_src _ _
      | some j => rfl
    exact hm.trans (show m = m ≫ (u₁.inv.app (H.obj K)).f i from
      (Category.comp_id m).symm)
  have hb : H.map (η₀.app K) ≫ g = b.hom ≫ η₁.app (H.obj K) :=
    mapExtendIso_hom_natTrans η e K
  have ha : (F.mapHomologicalComplex (.up ℤ)).map a ≫ η₁.app L =
      η₁.app (H.obj K) ≫ G₁.map a := η₁.naturality a
  have hcomp : H.map u₀.inv ≫ b.hom = u₁.inv.app (H.obj K) := by
    rw [hId, ← Category.assoc, ← H.map_comp, Iso.inv_hom_id, H.map_id, Category.id_comp]
  change H.map (u₀.inv ≫ η₀.app K) ≫ (g ≫ G₁.map a) =
    a ≫ (u₁.inv.app L ≫ η₁.app L)
  calc
    _ = H.map u₀.inv ≫ ((H.map (η₀.app K) ≫ g) ≫ G₁.map a) := by
      simp only [H.map_comp, Category.assoc]
    _ = (H.map u₀.inv ≫ b.hom) ≫ (η₁.app (H.obj K) ≫ G₁.map a) := by
      rw [hb]
      simp only [Category.assoc]
    _ = u₁.inv.app (H.obj K) ≫ ((F.mapHomologicalComplex (.up ℤ)).map a ≫ η₁.app L) :=
      congrArg₂ (· ≫ ·) hcomp ha.symm
    _ = _ := by
      simp only [← Category.assoc]
      exact congrArg (· ≫ η₁.app L) (u₁.inv.naturality a).symm

private theorem singularSheafCochainParameterSectionsMap_base
    (P : PresheafWithTransfers.{u + 1} k) :
    (singularSheafCochainFunctor k 0).map (baseSectionsPresheafIso k P).hom ≫
      singularSheafCochainParameterSectionsMap k B P =
        (baseSectionsSheafCochainIso k P).hom := by
  let e := ComplexShape.embeddingUpIntLE 0
  let A := nisnevichSheafify k
  let B₁ := (parameterSectionsFunctor k B).mapHomologicalComplex (.up ℤ)
  let E := e.extendFunctor (SheafWithTransfers.{u + 1} k)
  let D := e.extendFunctor (PresheafWithTransfers.{u + 1} k)
  let K := singularComplex P
  let K' := singularComplex (baseSections P)
  let a := mapExtendIso A e K
  let a' := mapExtendIso A e K'
  let b := mapExtendIso (parameterSectionsFunctor k B) e (singularSheafComplex k P)
  let r := singularComplexMap (baseSectionsPresheafIso k P).hom
  let m := singularSheafParameterSectionsMap k B P
  let A₀ := A.mapHomologicalComplex (.down ℕ)
  let A₁ := A.mapHomologicalComplex (.up ℤ)
  have hA : A₁.map (D.map r) ≫ a'.inv = a.inv ≫ E.map (A₀.map r) :=
    (mapExtendNatIso A e).inv.naturality r
  have hm : E.map (A₀.map r) ≫ E.map m = E.map (baseSectionsSheafComplexIso k P).hom :=
    (E.map_comp _ _).symm.trans (congrArg E.map (singularSheafParameterSectionsMap_base k P))
  change A₁.map (D.map r) ≫ (a'.inv ≫ E.map m ≫ b.hom ≫ B₁.map a.hom) = _
  simp only [reassoc_of% hA, reassoc_of% hm]
  have hb : E.map (baseSectionsSheafComplexIso k P).hom ≫ b.hom ≫ B₁.map a.hom =
      a.hom ≫ (baseSectionsSheafCochainIso k P).hom :=
    baseSectionsSheafComplexIso_extend k P
  exact (congrArg (a.inv ≫ ·) hb).trans (a.inv_hom_id_assoc _)

/-- The original cochain comparison intertwines restriction to the actual
unit with the raw unit restriction in base-product coordinates. -/
theorem singularSheafCochainTorusSectionsMap_comp_unit
    (P : PresheafWithTransfers.{u + 1} k) :
    singularSheafCochainTorusSectionsMap k P ≫
        (torusSectionsComplexUnitRestriction k).app (singularSheafCochainComplex k P 0) =
      (singularSheafCochainFunctor k 0).map
        (torusUnit P ≫ (baseSectionsPresheafIso k P).inv) := by
  let A := singularSheafCochainFunctor k 0
  let r := torusUnit P
  let b := baseSectionsPresheafIso k P
  let m := singularSheafCochainParameterSectionsMap k B P
  let K := singularSheafCochainComplex k P 0
  let c := baseSectionsSheafCochainIso k P
  let β := ((parameterSectionsPullbackNatTrans k (SmoothSite.torusOne S)).mapHomologicalComplex
    (.up ℤ)).app K
  have h : A.map r ≫ m = singularSheafCochainTorusSectionsMap k P ≫ β :=
    singularSheafCochainParameterSectionsMap_parameterMap k (SmoothSite.torusOne S) P
  have hc : A.map b.hom ≫ m = c.hom := singularSheafCochainParameterSectionsMap_base k P
  have hm : m ≫ c.inv = A.map b.inv := by
    apply (cancel_epi (A.map b.hom)).1
    rw [← Category.assoc, hc, Iso.hom_inv_id, ← A.map_comp, Iso.hom_inv_id, A.map_id]
  change singularSheafCochainTorusSectionsMap k P ≫ (β ≫ c.inv) = A.map (r ≫ b.inv)
  rw [← Category.assoc, ← h, Category.assoc, hm, A.map_comp]

variable [HasDerivedCategory.{w} (SheafWithTransfers.{u + 1} k)]

/-- The total derived comparison carries the original source unit map to
the actual derived unit restriction. -/
theorem singularSheafDerivedTorusSectionsMap_comp_unit
    (P : PresheafWithTransfers.{u + 1} k) :
    singularSheafDerivedTorusSectionsMap k P ≫
        (torusSectionsDerivedUnitRestriction k).app
          (DerivedCategory.Q.obj (singularSheafCochainComplex k P 0)) =
      DerivedCategory.Q.map ((singularSheafCochainFunctor k 0).map
        (torusUnit P ≫ (baseSectionsPresheafIso k P).inv)) := by
  rw [singularSheafDerivedTorusSectionsMap, Category.assoc,
    torusSectionsDerivedUnitRestriction_app_Q_obj, ← Functor.map_comp]
  exact congrArg DerivedCategory.Q.map (singularSheafCochainTorusSectionsMap_comp_unit k P)

end AlgebraicGeometry.SheafWithTransfers
