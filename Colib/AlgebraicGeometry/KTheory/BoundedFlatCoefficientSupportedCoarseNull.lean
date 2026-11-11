/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportModels
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOpenSections
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectOpenSupport
public import Colib.KTheory.Waldhausen.Iterated.DiagramZeroNull
public import Colib.Topology.Prespectrum.ConeDiagramDescent
/-! # The original ordinary supported coarse null and acyclic equivalence

The actual joint zero-to-inclusion is weak precisely by support acyclicity. Its complete
original reverse null descends from the same cone. The geometric acyclic equivalence and
both exact directions retain their actual objects. Initial cone stability is a later closure.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration
open CategoryTheory.Waldhausen.IteratedS AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.BaseChange.Coefficients Topology.LoopPrespectrum HomologicalComplex
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left]
/-- Realize the unchanged ambient identity change to coarse relative-open weakness. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportLocalizationModels.lean:167"
  "adaptation" "Original whole coarse null and actual supported acyclic equivalence"]
def boundedAboveFlatCoefficientAmbientOpenPrespectrumTransformation :
    boundedAboveFlatCoefficientAmbientPrespectrumFunctor Q ⟶
      boundedAboveFlatCoefficientOpenPrespectrumFunctor f :=
  Functor.whiskerRight (boundedAboveFlatCoefficientOpenChangeWeakModelTransformation f)
    prespectrumFunctor

/-- The unique original joint-zero-to-supported-inclusion transformation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportLocalizationModels.lean:174"
  "adaptation" "Original whole coarse null and actual supported acyclic equivalence"]
def boundedAboveFlatCoefficientSupportedZeroToOpen (a : Under R) :
    (Functor.const ((boundedAboveFlatCoefficientSectionSupported (schemeMap f
      a)).FullSubcategory)).obj
        (boundedAboveFlatCoefficientSectionWaldhausen (op Q, a)).zero ⟶
      (boundedAboveFlatCoefficientSectionSupported (schemeMap f a)).ι where
  app S := (boundedAboveFlatCoefficientSectionWaldhausen (op Q, a)).isZero.to_ S.obj
  naturality _ _ _ := (boundedAboveFlatCoefficientSectionWaldhausen (op Q, a)).isZero.eq_of_src _ _

/-- Actual support makes this exact original zero-to-image transformation coarse weak. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportLocalizationModels.lean:182"
  "adaptation" "Original whole coarse null and actual supported acyclic equivalence"]
theorem boundedAboveFlatCoefficientSupportedZeroToOpen_weak (a : Under R)
    (S : (boundedAboveFlatCoefficientSectionSupported (schemeMap f a)).FullSubcategory) :
    (boundedAboveFlatCoefficientOpenModel f a).obj.waldhausen.weq
      ((boundedAboveFlatCoefficientSupportedZeroToOpen f a).app S) := by
  have hZ : IsZero (((restrictFunctor (schemeMap f a)).mapHomologicalComplex (ComplexShape.up
    ℤ)).obj
      ((boundedAboveFlatCoefficientOriginalEvaluation (op Q, a)).obj
        (boundedAboveFlatCoefficientSectionWaldhausen (op Q, a)).zero).obj) :=
    ((restrictFunctor (schemeMap f a)).mapHomologicalComplex (ComplexShape.up ℤ)).map_isZero
      ((boundedAboveFlatPerfectComplex (space (op Q, a)).toRingedSpace).ι.map_isZero
      ((boundedAboveFlatCoefficientOriginalEvaluation_exact (op Q, a)).zero
        (boundedAboveFlatCoefficientSectionWaldhausen (op Q, a)).isZero))
  change QuasiIso (((restrictFunctor (schemeMap f a)).mapHomologicalComplex (ComplexShape.up ℤ)).map
    ((boundedAboveFlatCoefficientOriginalEvaluation (op Q, a)).map
      ((boundedAboveFlatCoefficientSupportedZeroToOpen f a).app S)).hom)
  rw [quasiIso_iff]
  intro n
  exact (quasiIsoAt_iff_exactAt _ n
    (HomologicalComplex.acyclic_of_isZero _ hZ n)).mpr (S.property n)

/-- Reverse the same weak zero-to-inclusion realization, retaining all original null times. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportLocalizationModels.lean:201"
  "adaptation" "Original whole coarse null and actual supported acyclic equivalence"]
def boundedAboveFlatCoefficientSupportedOpenDiagramNull :
    DiagramNullHomotopy (boundedAboveFlatCoefficientSupportedForgetPrespectrumTransformation f)
      (boundedAboveFlatCoefficientAmbientOpenPrespectrumTransformation f) :=
  modelDiagramZeroNull (boundedAboveFlatCoefficientSupportedForgetModelTransformation f)
    (boundedAboveFlatCoefficientOpenChangeWeakModelTransformation f)
    (fun a ↦ boundedAboveFlatCoefficientSupportedZeroToOpen f a)
    (fun a ↦ boundedAboveFlatCoefficientSupportedZeroToOpen_weak f a)

/-- The same complete original null descends from the original supported-inclusion cone. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportLocalizationModels.lean:210"
  "adaptation" "Original whole coarse null and actual supported acyclic equivalence"]
def boundedAboveFlatCoefficientSupportedOpenConeComparison :
    mappingConeDiagram (boundedAboveFlatCoefficientSupportedForgetPrespectrumTransformation f) ⟶
      boundedAboveFlatCoefficientOpenPrespectrumFunctor f :=
  mappingConeDescTransformation
    (boundedAboveFlatCoefficientSupportedForgetPrespectrumTransformation f)
    (boundedAboveFlatCoefficientAmbientOpenPrespectrumTransformation f)
    (boundedAboveFlatCoefficientSupportedOpenDiagramNull f).homotopy
    (boundedAboveFlatCoefficientSupportedOpenDiagramNull f).naturality

/-- Original supported evaluation followed by the actual geometric acyclic conversion. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportLocalizationModels.lean:219"
  "adaptation" "Original whole coarse null and actual supported acyclic equivalence"]
def boundedAboveFlatCoefficientSupportAcyclicEvaluation (a : Under R) :
    (boundedAboveFlatCoefficientSectionSupported (schemeMap f a)).FullSubcategory ⥤
      AcyclicCategory (boundedAboveFlatPerfectOpenNested (schemeMap f a)) :=
  boundedAboveFlatCoefficientSupportedEvaluation (schemeMap f a) ⋙
    boundedAboveFlatPerfectSupportedToAcyclic (schemeMap f a)

/-- Actual support evaluation is exact into the inherited fine acyclic Model. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportLocalizationModels.lean:226"
  "adaptation" "Original whole coarse null and actual supported acyclic equivalence"]
theorem boundedAboveFlatCoefficientSupportAcyclicEvaluation_exact (a : Under R) :
    IsExact (boundedAboveFlatCoefficientSupportedSectionWaldhausen (schemeMap f a)).cof
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen (schemeMap f a)).weq
      (acyclicStructure (boundedAboveFlatPerfectOpenNested (schemeMap f a))).cof
      (acyclicStructure (boundedAboveFlatPerfectOpenNested (schemeMap f a))).weq
      (boundedAboveFlatCoefficientSupportAcyclicEvaluation f a) :=
  (boundedAboveFlatCoefficientSupportedEvaluation_exact (schemeMap f a)).comp
    (boundedAboveFlatPerfectSupportedToAcyclic_exact (schemeMap f a))

/-- Evaluation preserves the actual supported inclusion before common-universe lifting. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportLocalizationModels.lean:236"
  "adaptation" "Original whole coarse null and actual supported acyclic equivalence"]
theorem boundedAboveFlatCoefficientSupportAcyclicEvaluation_inclusion (a : Under R) :
    boundedAboveFlatCoefficientSupportAcyclicEvaluation f a ⋙
        acyclicInclusion (boundedAboveFlatPerfectOpenNested (schemeMap f a)) =
      (boundedAboveFlatCoefficientSectionSupported (schemeMap f a)).ι ⋙
        boundedAboveFlatCoefficientOriginalEvaluation (op Q, a) := by
  rw [boundedAboveFlatCoefficientSupportAcyclicEvaluation, Functor.assoc,
    boundedAboveFlatPerfectSupportedToAcyclic_comp_inclusion,
    boundedAboveFlatPerfectSupportedForget,
    boundedAboveFlatCoefficientSupportedEvaluation_forget_to_boundedAboveFlat]

/-- The same actual supported-to-acyclic functor is the forward map of a genuine equivalence. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportLocalizationModels.lean:246"
  "adaptation" "Original whole coarse null and actual supported acyclic equivalence"]
def boundedAboveFlatCoefficientSupportAcyclicEquivalence (a : Under R) :
    (boundedAboveFlatCoefficientSectionSupported (schemeMap f a)).FullSubcategory ≌
      AcyclicCategory (boundedAboveFlatPerfectOpenNested (schemeMap f a)) :=
  ((boundedAboveFlatCoefficientSupportedSectionEquivalence (schemeMap f a)).trans
    (boundedAboveFlatPerfectAcyclicSupportedEquivalence (schemeMap f a)).symm).changeFunctor
      (eqToIso (congrArg (fun F ↦ F ⋙ boundedAboveFlatPerfectSupportedToAcyclic (schemeMap f a))
        (boundedAboveFlatCoefficientSupportedSectionEquivalence_functor (schemeMap f a))))

/-- Its original inverse retains the two proved exact inverse functors. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportLocalizationModels.lean:255"
  "adaptation" "Original whole coarse null and actual supported acyclic equivalence"]
theorem boundedAboveFlatCoefficientSupportAcyclicEquivalence_inverse_exact (a : Under R) :
    IsExact (acyclicStructure (boundedAboveFlatPerfectOpenNested (schemeMap f a))).cof
      (acyclicStructure (boundedAboveFlatPerfectOpenNested (schemeMap f a))).weq
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen (schemeMap f a)).cof
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen (schemeMap f a)).weq
      (boundedAboveFlatCoefficientSupportAcyclicEquivalence f a).inverse :=
  (boundedAboveFlatPerfectAcyclicToSupported_exact (schemeMap f a)).comp
    (boundedAboveFlatCoefficientSupportedSectionEquivalence_inverse_exact (schemeMap f a))

/-- The restricted joint zero evaluates to the inherited geometric acyclic zero literally. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportLocalizationModels.lean:265"
  "adaptation" "Original whole coarse null and actual supported acyclic equivalence"]
theorem boundedAboveFlatCoefficientSupportAcyclicEvaluation_zero (a : Under R) :
    (boundedAboveFlatCoefficientSupportAcyclicEvaluation f a).obj
        (boundedAboveFlatCoefficientSupportedModel f a).obj.waldhausen.zero =
      (acyclicStructure (boundedAboveFlatPerfectOpenNested (schemeMap f a))).zero := by
  apply ObjectProperty.FullSubcategory.ext
  have h := congrArg (fun F ↦ F.obj (boundedAboveFlatCoefficientSupportedModel f
    a).obj.waldhausen.zero)
    (boundedAboveFlatCoefficientSupportAcyclicEvaluation_inclusion f a)
  exact h.trans (boundedAboveFlatCoefficientOriginalEvaluation_sectionZero (op Q, a))

end AlgebraicGeometry.Scheme.Modules
