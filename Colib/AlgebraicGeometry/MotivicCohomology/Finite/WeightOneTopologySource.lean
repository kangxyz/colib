/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.DerivedCategory.SingleSourceTransport
public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneEtaleKernel
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.SourceSections

/-! # Original change of topology preserves the canonical weight-one source -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers
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
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Original Nisnevich-to-étale derived transport retains the actual degree-zero unit section. -/
lemma weightOneUnitsChangeOfTopology_source (X : SmoothSite (Spec (.of k)))
    (h : (freeYoneda.{u + 1} (nisnevichTopology (Spec (.of k)))).obj X ⟶
      largeUnitsSheaf (Spec (.of k))) :
    nisnevichToEtaleDerivedHomMap (Spec (.of k)) X (weightOneUnitsComplex k) 1
        ((DerivedCategory.singleFunctor _ 0).map h ≫
          (derivedSingleNegOneCancelIso (largeUnitsSheaf (Spec (.of k)))).inv) ≫
      (DerivedCategory.Q.map (weightOneUnitsChangeOfTopologyIso k).hom)⟦(1 : ℤ)⟧' ≫
      (derivedSingleNegOneCancelIso (largeUnitsEtaleSheaf (Spec (.of k)))).hom =
    (DerivedCategory.singleFunctor _ 0).map
      ((sectionsEquiv.{u + 1} X (largeUnitsEtaleSheaf (Spec (.of k)))).symm
        (sectionsEquiv.{u + 1} X (largeUnitsSheaf (Spec (.of k))) h)) := by
  have h₁ := derivedSourceTransport_singleMap_cancel
    (nisnevichToEtaleSheaf (Spec (.of k)) AddCommGrpCat.{u + 1}) _ _ _ _
    ((nisnevichToEtaleFreeYonedaIso (Spec (.of k))).inv.app X)
    (nisnevichToEtaleLargeUnitsIso (Spec (.of k))) h
  have h₂ := (Equiv.eq_symm_apply (sectionsEquiv.{u + 1} X (largeUnitsEtaleSheaf (Spec (.of k))))).2
    (nisnevichToEtaleFreeYonedaIso_units (Spec (.of k)) X h)
  change _ = (DerivedCategory.singleFunctor _ 0).map _
  rw [← h₂]
  have hi : weightOneUnitsChangeOfTopologyIso k =
      CochainComplex.finiteCoefficients.shiftedSingleFunctorIso
        (nisnevichToEtaleSheaf (Spec (.of k)) AddCommGrpCat.{u + 1})
        (largeUnitsSheaf (Spec (.of k))) (largeUnitsEtaleSheaf (Spec (.of k)))
        (nisnevichToEtaleLargeUnitsIso (Spec (.of k))) := rfl
  rw [hi]
  simpa only [nisnevichToEtaleDerivedHomMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    weightOneUnitsComplex, Category.assoc] using h₁

end AlgebraicGeometry.MotivicCohomology.WeightOne
