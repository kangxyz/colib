/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.Embedding.SingleComponent
public import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.ChainNormalization
public import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.TargetNormalization

/-!
# The raw degree-one component of the actual comparison

The transfer sheafification unit followed by the inverse underlying comparison
is the ordinary unit. This removes the only sheafification coordinate change
in the degree-one component of the actual signed weight-one map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite AlgebraicSimplex

universe u

namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme SmoothSite

/-- The actual inverse underlying comparison cancels the transfer sheafification unit. -/
@[reassoc] theorem toNisnevichSheafify_underlyingIso_inv
    (k : Type u) [Field k] (P : PresheafWithTransfers.{u + 1} k) :
    (toPresheaf k).map (toNisnevichSheafify k P) ≫
      ((nisnevichSheafificationUnderlyingIso k).inv.app P).hom =
        toSheafify (nisnevichTopology (Spec (.of k))) ((toPresheaf k).obj P) := by
  let e := (sheafToPresheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).mapIso
    ((nisnevichSheafificationUnderlyingIso k).app P)
  rw [← toSheafify_nisnevichSheafificationUnderlyingIso]
  change (toSheafify (nisnevichTopology (Spec (.of k))) ((toPresheaf k).obj P) ≫
    e.hom) ≫ e.inv = _
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The underlying ordinary singular comparison is retained until evaluation.
Its component on literal product sections is the identity, but its natural
transformation must first pass through ordinary sheafification naturality. -/
theorem toNisnevichSheafify_singularSheafOrdinaryIso_hom_app
    (k : Type u) [Field k] (P : PresheafWithTransfers.{u + 1} k)
    (n : ℕ) (X : SmoothSite (Spec (.of k))) :
    (((toPresheaf k).map (toNisnevichSheafify k ((singularComplex P).X n))).app
      (op X)) ≫ (((singularSheafOrdinaryIso k P).hom.f n).hom.app (op X)) =
    (toSheafify (nisnevichTopology (Spec (.of k)))
      (((singularChainsFunctor k).obj ((toPresheaf k).obj P)).X n)).app (op X) := by
  let J := nisnevichTopology (Spec (.of k))
  let α := (singularComplexUnderlyingIso P).hom.f n
  have hu := toNisnevichSheafify_underlyingIso_inv k ((singularComplex P).X n)
  have hα := toSheafify_naturality J α
  have h : (toPresheaf k).map (toNisnevichSheafify k ((singularComplex P).X n)) ≫
      ((singularSheafOrdinaryIso k P).hom.f n).hom =
      α ≫ toSheafify J (((singularChainsFunctor k).obj ((toPresheaf k).obj P)).X n) := by
    change (toPresheaf k).map (toNisnevichSheafify k ((singularComplex P).X n)) ≫
      ((nisnevichSheafificationUnderlyingIso k).inv.app ((singularComplex P).X n)).hom ≫
        sheafifyMap J α = _
    rw [← Category.assoc, hu]
    exact hα.symm
  have hx := congrArg (fun η => η.app (op X)) h
  simpa only [NatTrans.comp_app, α, singularComplexUnderlyingIso_hom_f_app,
    Category.id_comp] using hx

end AlgebraicGeometry.PresheafWithTransfers

namespace AlgebraicGeometry.MotivicCohomology.WeightOne
open _root_.AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers

variable (k : Type u) [Field k]

/-- The signed-shift degree-one component is the original ordinary chain-zero component. -/
theorem rawWeightOneComparison_f_one :
    (motivicRawBaseComplexXIso k 1 0).inv ≫
      (rawWeightOneComparison k).f 1 ≫ (shiftedUnitsBaseXIso k).hom =
    (toSheafify (nisnevichTopology (Spec (.of k)))
      ((rawReducedSingular k).X 0)).app (op (base (Spec (.of k)))) ≫
      (((weightOneSheafChainComparison k).f 0) ≫
        (HomologicalComplex.singleObjXSelf (.down ℕ) 0
          (largeUnitsSheaf (Spec (.of k)))).hom).hom.app (op (base (Spec (.of k)))) := by
  let K := singularComplex (reducedTorus k 1)
  let e := ComplexShape.embeddingUpIntLE 0
  have he : e.f (0 : ℕ) = (0 : ℤ) := by simp [e]
  let F := nisnevichSheafify k ⋙ SheafWithTransfers.toSheaf k
  let R := toPresheaf k ⋙
    (CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj
      (op (base (Spec (.of k))))
  let E := (sheafSections (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).obj
    (op (base (Spec (.of k))))
  let α := (singularSheafOrdinaryIso k (reducedTorus k 1)).hom
  let β := weightOneSheafChainComparison k
  let A := largeUnitsSheaf (Spec (.of k))
  let t := (Stacks.DerivedIndexing.mapExtendIso F e K).inv.f 0 ≫
    (HomologicalComplex.extendMap α e).f 0 ≫
    (HomologicalComplex.extendMap β e).f 0 ≫
    (HomologicalComplex.extendSingleIso e A 0 0 he).hom.f 0 ≫
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).hom
  have hn : R.map (K.extendXIso e he).inv ≫
      R.map (toNisnevichSheafify k ((K.extend e).X 0)) =
      R.map (toNisnevichSheafify k (K.X 0)) ≫
        E.map (F.map (K.extendXIso e he).inv) := by
    have h := congrArg (fun η => R.map η)
      (toNisnevichSheafify_naturality k (K.extendXIso e he).inv)
    simpa only [Functor.map_comp] using h
  have hc : F.map (K.extendXIso e he).inv ≫ t =
      α.f 0 ≫ β.f 0 ≫ (HomologicalComplex.singleObjXSelf (.down ℕ) 0 A).hom :=
    HomologicalComplex.map_extend_single_component F e he K _ A α β
  have hu := toNisnevichSheafify_singularSheafOrdinaryIso_hom_app k
    (reducedTorus k 1) 0 (base (Spec (.of k)))
  calc
    _ = R.map (K.extendXIso e he).inv ≫
        R.map (toNisnevichSheafify k ((K.extend e).X 0)) ≫ E.map t := by
      -- Only the shift/evaluation wrappers are unfolded here. All extension
      -- coordinates and the full ordinary singular comparison remain in t.
      simp [rawWeightOneComparison, motivicRawBaseComplexIso,
        motivicBaseSheafificationIso, weightOneSheafComparison,
        motivicSheafComplexOrdinaryShiftIso, motivicRawBaseComplexXIso,
        singularShiftedCochainXIso, HomologicalComplex.ExtensionSignedShift.shiftedXIso,
        shiftedUnitsBaseXIso_hom, Functor.mapCochainComplexShiftIso,
        K, e, F, R, E, α, β, A, t, Functor.map_comp, Category.assoc]
    _ = R.map (toNisnevichSheafify k (K.X 0)) ≫
        E.map (F.map (K.extendXIso e he).inv ≫ t) := by
      rw [E.map_comp, ← Category.assoc, ← hn, Category.assoc]
    _ = R.map (toNisnevichSheafify k (K.X 0)) ≫
        E.map (α.f 0 ≫ β.f 0 ≫
          (HomologicalComplex.singleObjXSelf (.down ℕ) 0 A).hom) := by rw [hc]
    _ = _ := by
      rw [E.map_comp, ← Category.assoc]
      change (((toPresheaf k).map (toNisnevichSheafify k (K.X 0))).app
        (op (base (Spec (.of k)))) ≫
        ((singularSheafOrdinaryIso k (reducedTorus k 1)).hom.f 0).hom.app
          (op (base (Spec (.of k))))) ≫ _ = _
      rw [hu]

/-- Pulling a literal reduced section to the zero simplex introduces no extra coefficient
or sign. -/
theorem rawWeightOneComparison_zero_pullback
    (s : (rawReducedTorus k).obj (op (base (Spec (.of k))))) :
    (shiftedUnitsBaseXIso k).hom
      ((rawWeightOneComparison k).f 1
        ((motivicRawBaseComplexXIso k 1 0).inv
          ((rawReducedTorus k).map
            (productFst (base (Spec (.of k))) (smoothSiteObj k 0)).op s))) =
      (reducedNorm k).app (op (base (Spec (.of k)))) s := by
  have h := congrArg
    (fun f => (rawReducedTorus k).map
      (productFst (base (Spec (.of k))) (smoothSiteObj k 0)).op ≫ f)
    (rawWeightOneComparison_f_one k)
  rw [rawChainComparison_zero_pullback] at h
  exact ConcreteCategory.congr_hom h s

end AlgebraicGeometry.MotivicCohomology.WeightOne
