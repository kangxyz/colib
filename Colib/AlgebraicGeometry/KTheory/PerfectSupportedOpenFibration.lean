/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectSupportedRestriction
public import Colib.AlgebraicGeometry.Modules.PerfectSupportedJoint
public import Colib.CategoryTheory.Waldhausen.Fibration.CofibrationClosedExtension
public import Colib.CategoryTheory.Waldhausen.Fibration.ComplexExtension
public import Colib.KTheory.Waldhausen.Fibration.GeneralComparison

/-!
# Genuine relative-open fibration with prescribed support

Weakness is detected by actual open restriction; the original supported category,
cofibrations and zero are unchanged. Genuine native cone closure and the explicit
cylinder prove the full canonical fiber comparison. The coarse target is not fine
K-theory of the supported open. No geometric or compactness hypothesis is used.
Adapted from Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/Fibration.lean
at c561118b7795eb9780be9ed391c3251d6a4d0afd.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- The original supported perfect category, cofibrations and chosen zero, with weak
equivalences detected by actual open restriction. -/
def perfectSupportedOpenWeakWaldhausen : Waldhausen.Structure (perfectSupported T.ι).FullSubcategory
  :=
  Waldhausen.Structure.withInverseImageWeak (perfectSupportedRestrict_exact j T)

/-- Genuine fine quasi-isomorphisms are contained in the actual relative class. -/
def perfectSupportedOpenNested : Waldhausen.Fibration.NestedWeakEquivalences
  (perfectSupportedWaldhausen T.ι) :=
  Waldhausen.Structure.inverseImageWeakNested (perfectSupportedRestrict_exact j T)

@[simp] theorem perfectSupportedOpenWeakWaldhausen_cof :
    (perfectSupportedOpenWeakWaldhausen j T).cof = (perfectSupportedWaldhausen T.ι).cof := rfl

@[simp] theorem perfectSupportedOpenWeakWaldhausen_zero :
    (perfectSupportedOpenWeakWaldhausen j T).zero = (perfectSupportedWaldhausen T.ι).zero := rfl

/-- The relative weak predicate is precisely quasi-isomorphism on the actual
restricted underlying chain map. -/
@[simp] theorem perfectSupportedOpenWeakWaldhausen_weq_iff {K L : (perfectSupported
  T.ι).FullSubcategory} (f : K ⟶ L) :
    (perfectSupportedOpenWeakWaldhausen j T).weq f ↔
      QuasiIso (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map f.hom) :=
  Iff.rfl

instance perfectSupportedOpenWeakWaldhausen_twoOutOfThree :
    (perfectSupportedOpenWeakWaldhausen j T).weq.HasTwoOutOfThreeProperty := by
  let : MorphismProperty.HasTwoOutOfThreeProperty (Waldhausen.complexes U.Modules).weq := by
    change (HomologicalComplex.quasiIso U.Modules (ComplexShape.up ℤ)).HasTwoOutOfThreeProperty
    infer_instance
  let : (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).weq.HasTwoOutOfThreeProperty :=
    Waldhausen.CofibrationClosedSubcategory.twoOutOfThree _ _ _
  exact Waldhausen.Structure.withInverseImageWeak_twoOutOfThree
    (perfectSupportedRestrict_exact j T)

instance perfectSupportedOpenNested_twoOutOfThree :
    (perfectSupportedOpenNested j T).coarse.weq.HasTwoOutOfThreeProperty :=
  perfectSupportedOpenWeakWaldhausen_twoOutOfThree j T

/-- The extension axiom follows from actual exact open restriction. -/
theorem perfectSupportedOpenWeakWaldhausen_extensionAxiom :
    Waldhausen.Fibration.ExtensionAxiom (perfectSupportedOpenWeakWaldhausen j T) :=
  Waldhausen.Structure.withInverseImageWeak_extensionAxiom
    (perfectSupportedRestrict_exact j T)
    (Waldhausen.CofibrationClosedSubcategory.extensionAxiom _ _
      (perfectSupported_cofibrationClosed (j ⁻¹ᵁ T).ι)
      Waldhausen.Fibration.complexes_extensionAxiom)

/-- The original restriction functor is also exact for the relative model. -/
theorem perfectSupportedOpenRestrict_waldhausenExact :
    Waldhausen.IsExact (perfectSupportedOpenWeakWaldhausen j T).cof
      (perfectSupportedOpenWeakWaldhausen j T).weq
      (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).cof (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).weq
        (perfectSupportedRestrict j T) :=
  Waldhausen.Structure.withInverseImageWeak_exact (perfectSupportedRestrict_exact j T)

/-- The actual identity-cone joint cylinder in supported locally perfect complexes. -/
def perfectSupportedOpenJointData : Waldhausen.Fibration.RowFactorization.JointData
  (perfectSupportedOpenNested j T) :=
  perfectSupportedJointData T.ι (perfectSupportedOpenNested j T)

/-- The actual target endpoint is a section of the original cylinder projection. -/
theorem perfectSupportedOpenJointData_secondEndpointSection :
    Waldhausen.Fibration.RowFactorization.SecondEndpointSection (perfectSupportedOpenNested j T)
      (perfectSupportedOpenJointData j T) :=
  perfectSupportedJointData_secondEndpointSection T.ι (perfectSupportedOpenNested j T)

/-- The unchanged original canonical relative-coarse fiber map is a weak
homotopy equivalence, without any common-universe or geometric extra hypothesis. -/
theorem perfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence
      (Waldhausen.Fibration.canonicalFiberMap (perfectSupportedOpenNested j T)) :=
  Waldhausen.Fibration.canonicalFiberMap_isWeakHomotopyEquivalence_general
    (perfectSupportedOpenNested j T) (perfectSupportedOpenWeakWaldhausen_extensionAxiom j T)
    (perfectSupportedOpenJointData j T) (perfectSupportedOpenJointData_secondEndpointSection j T)

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0331",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/Fibration.lean:31-103"
    "adaptation"
    "Native supported relative-open coarse model and actual maps, without fine-open comparison"]
  AlgebraicGeometry.Scheme.Modules.perfectSupportedOpenNested
  AlgebraicGeometry.Scheme.Modules.perfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence
