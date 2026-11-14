/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.DerivedCategory.ProjectiveSingleCoordinate
public import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.TargetNormalization
public import Colib.AlgebraicGeometry.Sites.Smooth.Hypercohomology.FieldEvaluation

/-! # Original projective representatives in the shifted weight-one units complex -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme SmoothSite CochainComplex.HomComplex
open Stacks.Cohomology.FreeYonedaUnivLE Stacks.Cohomology.Corepresented
universe w u
namespace AlgebraicGeometry.MotivicCohomology.WeightOne
variable (k : Type u) [Field k]
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

local instance : ((sheafSections (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).obj
    (op (base (Spec (.of k))))).Additive :=
  Functor.additive_of_iso (coyonedaIsoSheafSections.{u + 1}
    (nisnevichTopology (Spec (.of k))) (base (Spec (.of k))))

/-- Original projective Hom-complex representatives have the original degree-one unit coordinate. -/
lemma shiftedUnitsBaseHomologyIso_cocycle
    (z : Cocycle ((CochainComplex.singleFunctor _ 0).obj
      ((freeYoneda.{u + 1} (nisnevichTopology (Spec (.of k)))).obj
        (base (Spec (.of k))))) (shiftedUnitsSheafComplex k) 1) :
    (shiftedUnitsBaseHomologyIso k).hom
      (HomologicalComplex.homologyMap
        (corepresentedHomComplexIso
          ((sheafSections (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).obj
            (op (base (Spec (.of k))))) _
          (coyonedaIsoSheafSections.{u + 1} (nisnevichTopology (Spec (.of k)))
            (base (Spec (.of k)))) (shiftedUnitsSheafComplex k)).hom 1
        ((homologyAddEquiv _ _ 1).symm (CohomologyClass.mk z))) =
    sectionsEquiv.{u + 1} (base (Spec (.of k))) (largeUnitsSheaf (Spec (.of k)))
      (Cochain.fromSingleEquiv (zero_add 1) z.1 ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0
          (largeUnitsSheaf (Spec (.of k)))).hom) := by
  let I := corepresentedHomComplexIso
    ((sheafSections (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).obj
      (op (base (Spec (.of k))))) _
    (coyonedaIsoSheafSections.{u + 1} (nisnevichTopology (Spec (.of k)))
      (base (Spec (.of k)))) (shiftedUnitsSheafComplex k)
  rw [homologyAddEquiv_symm_mk]
  let P := (CochainComplex.singleFunctor _ 0).obj
    ((freeYoneda.{u + 1} (nisnevichTopology (Spec (.of k)))).obj
      (base (Spec (.of k))))
  change (((leftHomologyData P (shiftedUnitsSheafComplex k) 1).cyclesIso.inv ≫
    (P.HomComplex (shiftedUnitsSheafComplex k)).homologyπ 1 ≫
    HomologicalComplex.homologyMap I.hom 1 ≫ (shiftedUnitsBaseHomologyIso k).hom) z) = _
  rw [HomologicalComplex.homologyπ_naturality_assoc]
  erw [homologyπ_shiftedUnitsBaseHomologyIso k]
  erw [HomologicalComplex.cyclesMap_i_assoc I.hom 1]
  erw [ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles_assoc]
  rw [shiftedUnitsBaseXIso_hom]
  change ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (largeUnitsSheaf (Spec (.of k)))).hom.hom.app (op (base (Spec (.of k)))))
    (sectionsEquiv.{u + 1} (base (Spec (.of k))) _
      (Cochain.fromSingleEquiv (zero_add 1) z.1)) = _
  exact (sectionsEquiv_naturality _ _ _).symm

variable [HasDerivedCategory.{w}
  (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The original field hypercohomology comparison reads the actual localized cocycle coordinate. -/
lemma shiftedUnitsBaseHomologyIso_hypercohomology_cocycle
    (z : Cocycle ((CochainComplex.singleFunctor _ 0).obj
      ((freeYoneda.{u + 1} (nisnevichTopology (Spec (.of k)))).obj
        (base (Spec (.of k))))) (shiftedUnitsSheafComplex k) 1) :
    (shiftedUnitsBaseHomologyIso k).hom
      (hypercohomologyBaseFieldAddEquiv k (shiftedUnitsSheafComplex k) 1
        (((DerivedCategory.singleFunctorIsoCompQ _ 0).app
          ((freeYoneda.{u + 1} (nisnevichTopology (Spec (.of k)))).obj
            (base (Spec (.of k))))).hom ≫
          DerivedCategory.Q.map (Cocycle.equivHomShift.symm z) ≫
          (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (shiftedUnitsSheafComplex k))) =
    sectionsEquiv.{u + 1} (base (Spec (.of k))) (largeUnitsSheaf (Spec (.of k)))
      (Cochain.fromSingleEquiv (zero_add 1) z.1 ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0
          (largeUnitsSheaf (Spec (.of k)))).hom) := by
  let := projective_freeYoneda_base k
  let E := (sheafSections (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).obj
    (op (base (Spec (.of k))))
  let e := coyonedaIsoSheafSections.{u + 1} (nisnevichTopology (Spec (.of k)))
    (base (Spec (.of k)))
  rw [← projectiveHomologyDerivedAddEquiv_cocycle E _ e (shiftedUnitsSheafComplex k) 1 z]
  change (shiftedUnitsBaseHomologyIso k).hom
    ((projectiveHomologyDerivedAddEquiv E _ e (shiftedUnitsSheafComplex k) 1).symm
      ((projectiveHomologyDerivedAddEquiv E _ e (shiftedUnitsSheafComplex k) 1) _)) = _
  rw [AddEquiv.symm_apply_apply]
  exact shiftedUnitsBaseHomologyIso_cocycle k z

/-- Every original weight-one source map cancels to the single map of its actual field section. -/
lemma hypercohomology_shiftedUnits_source
    (x : (DerivedCategory.singleFunctor _ 0).obj
      ((freeYoneda.{u + 1} (nisnevichTopology (Spec (.of k)))).obj
        (base (Spec (.of k)))) ⟶ (DerivedCategory.Q.obj (shiftedUnitsSheafComplex k))⟦(1 : ℤ)⟧) :
    x ≫ (derivedSingleNegOneCancelIso (largeUnitsSheaf (Spec (.of k)))).hom =
      (DerivedCategory.singleFunctor _ 0).map
        ((sectionsEquiv.{u + 1} (base (Spec (.of k))) (largeUnitsSheaf (Spec (.of k)))).symm
          ((shiftedUnitsBaseHomologyIso k).hom
            (hypercohomologyBaseFieldAddEquiv k (shiftedUnitsSheafComplex k) 1 x))) := by
  let := projective_freeYoneda_base k
  let E := (sheafSections (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).obj
    (op (base (Spec (.of k))))
  let e := coyonedaIsoSheafSections.{u + 1} (nisnevichTopology (Spec (.of k)))
    (base (Spec (.of k)))
  obtain ⟨z, rfl⟩ := projectiveDerived_cocycle_surjective E _ e (shiftedUnitsSheafComplex k) 1 x
  rw [shiftedUnitsBaseHomologyIso_hypercohomology_cocycle, Equiv.symm_apply_apply]
  simpa only [Category.assoc] using localized_single_cocycle_cancel _ _ z

end AlgebraicGeometry.MotivicCohomology.WeightOne
