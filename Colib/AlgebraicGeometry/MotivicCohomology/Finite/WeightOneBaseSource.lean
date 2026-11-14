/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.SourceCoordinates
public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneTopologySource
public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneFullSmallSource

/-! # The original base-field weight-one source survives both site changes -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers
open AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open Stacks.Cohomology.FreeYonedaUnivLE Stacks.Cohomology.Corepresented
universe u wN wE wS
namespace AlgebraicGeometry.MotivicCohomology.WeightOne
variable (k : Type u) [Field k]
variable [HasSheafify (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}]
variable [HasSheafify (SmoothSite.etaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1}]
variable [HasDerivedCategory.{wN}
  (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{wE}
  (Sheaf (SmoothSite.etaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
variable [hSmall : HasDerivedCategory.{wS}
  (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1})]
/-- Reuse the given small-etale derived category at the definitional base object. -/
@[reducible] local instance weightOneBaseSourceSmallDerived : HasDerivedCategory.{wS}
    (Sheaf (base (Spec (.of k))).left.smallEtaleTopology AddCommGrpCat.{u + 1}) := hSmall
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Both original site comparisons preserve the actual normalized source unit of any class. -/
lemma weightOneBaseFullSmall_source
    (z : (DerivedCategory.singleFunctor _ 0).obj
      ((freeYoneda.{u + 1} (nisnevichTopology (Spec (.of k)))).obj (base (Spec (.of k)))) ⟶
        (DerivedCategory.Q.obj (shiftedUnitsSheafComplex k))⟦(1 : ℤ)⟧) :
    fullSmallDerivedHomMapAtBase (base (Spec (.of k))) (weightOneEtaleUnitsComplex k) 1
        (nisnevichToEtaleDerivedHomMap (Spec (.of k)) (base (Spec (.of k)))
            (weightOneUnitsComplex k) 1 z ≫
          (DerivedCategory.Q.map (weightOneUnitsChangeOfTopologyIso k).hom)⟦(1 : ℤ)⟧') ≫
      (DerivedCategory.Q.map
        (fullSmallEtaleUnitsComplexIso k (base (Spec (.of k)))).hom)⟦(1 : ℤ)⟧' ≫
      (derivedSingleNegOneCancelIso
        (Stacks.Kummer.multiplicativeSheaf.{u, 0} (Spec (.of k)))).hom =
    (DerivedCategory.singleFunctor _ 0).map
      ((sectionsEquiv.{u + 1} (Scheme.Etale.mk (𝟙 (Spec (.of k))))
        (Stacks.Kummer.multiplicativeSheaf.{u, 0} (Spec (.of k)))).symm
        (ULift.up ((shiftedUnitsBaseHomologyIso k).hom
          (hypercohomologyBaseFieldAddEquiv k (shiftedUnitsSheafComplex k) 1 z)).down)) := by
  let s := (shiftedUnitsBaseHomologyIso k).hom
    (hypercohomologyBaseFieldAddEquiv k (shiftedUnitsSheafComplex k) 1 z)
  let h := (sectionsEquiv.{u + 1} (base (Spec (.of k)))
    (largeUnitsSheaf (Spec (.of k)))).symm s
  let hE := (sectionsEquiv.{u + 1} (base (Spec (.of k)))
    (largeUnitsEtaleSheaf (Spec (.of k)))).symm s
  have hz : z = (DerivedCategory.singleFunctor _ 0).map h ≫
      (derivedSingleNegOneCancelIso (largeUnitsSheaf (Spec (.of k)))).inv := by
    calc
      z = (z ≫ (derivedSingleNegOneCancelIso (largeUnitsSheaf (Spec (.of k)))).hom) ≫
          (derivedSingleNegOneCancelIso (largeUnitsSheaf (Spec (.of k)))).inv := by
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      _ = _ := by rw [hypercohomology_shiftedUnits_source k z]
  have he : nisnevichToEtaleDerivedHomMap (Spec (.of k)) (base (Spec (.of k)))
          (weightOneUnitsComplex k) 1 z ≫
        (DerivedCategory.Q.map (weightOneUnitsChangeOfTopologyIso k).hom)⟦(1 : ℤ)⟧' =
      (DerivedCategory.singleFunctor _ 0).map hE ≫
        (derivedSingleNegOneCancelIso (largeUnitsEtaleSheaf (Spec (.of k)))).inv := by
    rw [hz]
    apply (cancel_mono (derivedSingleNegOneCancelIso (largeUnitsEtaleSheaf (Spec (.of k)))).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    simpa only [h, hE, Equiv.apply_symm_apply] using
      weightOneUnitsChangeOfTopology_source k (base (Spec (.of k))) h
  rw [he]
  have hs : sectionsEquiv.{u + 1} (base (Spec (.of k)))
      (largeUnitsEtaleSheaf (Spec (.of k))) hE = s :=
    (sectionsEquiv.{u + 1} (base (Spec (.of k)))
      (largeUnitsEtaleSheaf (Spec (.of k)))).apply_symm_apply s
  have hf := fullSmallUnits_source k (base (Spec (.of k))) hE
  rw [hs] at hf
  convert hf using 1 <;> rfl

end AlgebraicGeometry.MotivicCohomology.WeightOne
