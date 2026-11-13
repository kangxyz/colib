/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.ParameterProduct
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.TorusEvaluation
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSheafification.Singular

/-!
# The ordinary comparison of the transfer parameter product

The same signed simplex permutation and the same Nisnevich
sheafification unit determine the parameter map before the weight
shift. Forgetting transfers preserves those component formulas.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Jₖ" => SmoothSite.nisnevichTopology Sₖ
local notation "Gₘ" => SmoothSite.multiplicativeGroupObject Sₖ
local notation "F" => SheafWithTransfers.toSheaf k
local notation "A" => nisnevichSheafify k
local notation "B" => SheafWithTransfers.torusSectionsFunctor k
local notation "O" => torusParameterSheafFunctor k
local notation "T" => SmoothSite.Contraction.parameterProduct Gₘ
local notation "U" => toPresheaf k
local notation "c" => ComplexShape.down ℕ

/-- Multiply by the original parameter after retaining the signed
transfer action through singular chains and sheafification. -/
def transferReducedTorusSingularParameterProduct (q : ℕ) :
    singularSheafComplex k (reducedTorus k q) ⟶
      ((B).mapHomologicalComplex c).obj (singularSheafComplex k (reducedTorus k (q + 1))) :=
  (singularSheafFunctor k).map (reducedTorusParameterProduct k q) ≫
    SheafWithTransfers.singularSheafTorusSectionsMap k (reducedTorus k (q + 1))

private theorem transferReducedTorusSingularParameterProduct_unit (q n : ℕ) :
    toNisnevichSheafify k ((singularComplex (reducedTorus k q)).X n) ≫
      ((transferReducedTorusSingularParameterProduct k q).f n).hom =
      (singularComplexMap (reducedTorusParameterProduct k q)).f n ≫
        (withParameterSingularComplexIso (reducedTorus k (q + 1)) Gₘ).inv.f n ≫
        (withParameterFunctor Gₘ).map
          (toNisnevichSheafify k ((singularComplex (reducedTorus k (q + 1))).X n)) := by
  let a := (singularComplexMap (reducedTorusParameterProduct k q)).f n
  let Q := reducedTorus k (q + 1)
  let g := (SheafWithTransfers.singularSheafTorusSectionsMap k Q).f n
  change toNisnevichSheafify k _ ≫ (((A).map a).hom ≫ g.hom) = _
  rw [← Category.assoc, ← toNisnevichSheafify_naturality k a, Category.assoc]
  exact congrArg (a ≫ ·) (SheafWithTransfers.singularSheafTorusSectionsMap_unit k Q n)

private theorem transferReducedTorusRawParameterProduct_app (q n : ℕ)
    (X : SmoothSite Sₖ) :
    (((singularComplexMap (reducedTorusParameterProduct k q)).f n ≫
      (withParameterSingularComplexIso (reducedTorus k (q + 1)) Gₘ).inv.f n).hom.app
        (op (Cor.mk X))) =
      ((reducedTorusSingularParameterProduct k q).f n).app (op X) := by
  let Q := reducedTorus k (q + 1)
  let Y := AlgebraicSimplex.smoothSiteObj k n
  let f := SmoothSite.productSwapLast X Gₘ Y
  let m := reducedTorusParameterProduct k q
  rw [reducedTorusSingularParameterProduct_f_app]
  change m.hom.app (op (Cor.mk (SmoothSite.product X Y))) ≫
      transfer Q ((Cor.graphFunctor k).map f) = _
  rfl

private theorem ordinarySingularUnit (P : PresheafWithTransfers.{u + 1} k) (n : ℕ) :
    toSheafify Jₖ
      (((AlgebraicSimplex.singularChainsFunctor k).obj ((U).obj P)).X n) ≫
        ((singularSheafOrdinaryIso k P).inv.f n).hom =
      (singularComplexUnderlyingIso P).inv.f n ≫
        (U).map (toNisnevichSheafify k ((singularComplex P).X n)) := by
  let Pₙ := (singularComplex P).X n
  let e := nisnevichSheafificationUnderlyingIso k
  let a := presheafToSheaf Jₖ AddCommGrpCat.{u + 1}
  let b := (singularComplexUnderlyingIso P).inv.f n
  let w := (e.hom.app Pₙ).hom
  change toSheafify Jₖ _ ≫ ((a.map b).hom ≫ w) = b ≫ _
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc]
  exact congrArg (b ≫ ·) (toSheafify_nisnevichSheafificationUnderlyingIso k Pₙ)

/-- Forgetting transfers gives the original ordinary parameter product
before applying the signed weight shifts. -/
theorem transferReducedTorusSingularParameterProduct_underlying (q : ℕ) :
    ((F).mapHomologicalComplex c).map (transferReducedTorusSingularParameterProduct k q) ≫
      (NatIso.mapHomologicalComplex (SheafWithTransfers.torusSectionsToSheafIso k) c).hom.app
        (singularSheafComplex k (reducedTorus k (q + 1))) ≫
      ((O).mapHomologicalComplex c).map (singularSheafOrdinaryIso k (reducedTorus k (q + 1))).hom =
    (singularSheafOrdinaryIso k (reducedTorus k q)).hom ≫
      sheafifiedReducedTorusSingularParameterProduct k q := by
  let P := reducedTorus k q
  let Q := reducedTorus k (q + 1)
  let t := transferReducedTorusSingularParameterProduct k q
  let g := sheafifiedReducedTorusSingularParameterProduct k q
  let e := singularSheafOrdinaryIso k P
  let d := singularSheafOrdinaryIso k Q
  let φ := SheafWithTransfers.torusSectionsToSheafIso k
  let J := Jₖ
  ext n : 1
  apply (cancel_epi (e.inv.f n)).1
  apply ObjectProperty.hom_ext
  let Y := (((O).mapHomologicalComplex c).obj
    ((AlgebraicSimplex.sheafifiedSingularChainsFunctor k J).obj ((U).obj Q))).X n
  apply sheafify_hom_ext J _ _ Y.property
  let PN := (singularComplex P).X n
  let QN := (singularComplex Q).X n
  let uP := toSheafify J (((AlgebraicSimplex.singularChainsFunctor k).obj ((U).obj P)).X n)
  let uQ := toSheafify J (((AlgebraicSimplex.singularChainsFunctor k).obj ((U).obj Q)).X n)
  let vP := (U).map (toNisnevichSheafify k PN)
  let vQ := (U).map (toNisnevichSheafify k QN)
  let x := (U).map (t.f n).hom
  let y := (φ.hom.app ((A).obj QN)).hom
  let p := (e.inv.f n).hom
  let z := (d.hom.f n).hom
  let f := (g.f n).hom
  let bP := (singularComplexUnderlyingIso P).inv.f n
  let bQ := (singularComplexUnderlyingIso Q).inv.f n
  have hp : uP ≫ p = bP ≫ vP := ordinarySingularUnit k P n
  have hz : bQ ≫ vQ ≫ z = uQ := by
    have hh := ordinarySingularUnit k Q n
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ z) hh).symm.trans
      ((Category.assoc _ _ _).trans
        ((congrArg (uQ ≫ ·) (congrArg (fun m => m.hom)
          ((HomologicalComplex.eval _ c n).mapIso d).inv_hom_id)).trans (Category.comp_id _))))
  have hg : uP ≫ f = (reducedTorusSingularParameterProduct k q).f n ≫
      Functor.whiskerLeft (T).op uQ :=
    toSheafify_sheafifiedReducedTorusSingularParameterProduct_f k q n
  let m := (singularComplexMap (reducedTorusParameterProduct k q)).f n
  let σ := (withParameterSingularComplexIso Q Gₘ).inv.f n
  let u := toNisnevichSheafify k QN
  let T' := withParameterFunctor Gₘ
  have ht : vP ≫ x = (U).map (m ≫ σ) ≫ (U).map (T'.map u) := by
    rw [← (U).map_comp, ← (U).map_comp]
    exact (U).congr_map (transferReducedTorusSingularParameterProduct_unit k q n)
  let z' := Functor.whiskerLeft (T).op z
  let uQ' := Functor.whiskerLeft (T).op uQ
  let p' := (e.hom.f n).hom
  let g₀ := (reducedTorusSingularParameterProduct k q).f n
  let a₀ := (U).map (m ≫ σ)
  let a₁ := (U).map (T'.map u)
  have he : p ≫ p' = 𝟙 _ :=
    congrArg (fun m => m.hom) ((HomologicalComplex.eval _ c n).mapIso e).inv_hom_id
  have hright : uP ≫ ((p ≫ p') ≫ f) = g₀ ≫ uQ' :=
    (congrArg (fun m => uP ≫ m ≫ f) he).trans
      ((congrArg (uP ≫ ·) (Category.id_comp f)).trans hg)
  have hleft : uP ≫ (p ≫ x ≫ y ≫ z') = bP ≫ (a₀ ≫ a₁) ≫ y ≫ z' := by
    calc
      _ = (uP ≫ p) ≫ x ≫ y ≫ z' := (Category.assoc _ _ _).symm
      _ = (bP ≫ vP) ≫ x ≫ y ≫ z' := congrArg (· ≫ x ≫ y ≫ z') hp
      _ = bP ≫ (vP ≫ x) ≫ y ≫ z' := by simp only [Category.assoc]
      _ = _ := congrArg (fun m => bP ≫ m ≫ y ≫ z') ht
  change uP ≫ (p ≫ x ≫ y ≫ z') = uP ≫ ((p ≫ p') ≫ f)
  refine hleft.trans ((?_ : bP ≫ (a₀ ≫ a₁) ≫ y ≫ z' = g₀ ≫ uQ').trans hright.symm)
  apply NatTrans.ext
  funext X
  let X' := (T).op.obj X
  have hX := transferReducedTorusRawParameterProduct_app k q n X.unop
  have hQ : bQ.app X' ≫ vQ.app X' ≫ z.app X' = uQ.app X' :=
    NatTrans.congr_app hz X'
  have hQ' : vQ.app X' ≫ z.app X' = uQ.app X' :=
    (Category.id_comp _).symm.trans hQ
  change 𝟙 _ ≫ ((m ≫ σ).hom.app (op (Cor.mk X.unop)) ≫ vQ.app X') ≫
      𝟙 _ ≫ z.app X' = g₀.app X ≫ uQ.app X'
  calc
    _ = (m ≫ σ).hom.app (op (Cor.mk X.unop)) ≫ (vQ.app X' ≫ z.app X') := by
      simp only [Category.id_comp, Category.assoc]
    _ = _ := congrArg₂ (· ≫ ·) hX hQ'

end AlgebraicGeometry.PresheafWithTransfers
