/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionAcyclicEvaluation
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionOpenComparison
public import Colib.CategoryTheory.Waldhausen.AsSmall.Composition

/-!
# Original supported-section comparison with geometric relative acyclics

The actual exact equivalence is lifted to the original common universe. Its inherited-zero
identity supplies the same forward Model arrow, and its actual categorical inverse proves
complete levelwise weakness. The literal support-inclusion square is retained for the whole
null-track and cone comparison; no full-open endpoint identification is inferred.
-/
@[expose] public section

open CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.Fibration
open CategoryTheory.Waldhausen.IteratedS

noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Modules
open CategoryTheory.Waldhausen.SmallWaldhausenCategory AlgebraicGeometry.RingedSpace Topology
open Waldhausen Waldhausen.Fibration Waldhausen.IteratedS
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
attribute [local irreducible] boundedAboveFlatAffineOriginalEvaluation
  boundedAboveFlatAffineSupportedSectionEquivalence boundedAboveFlatAffineSupportedEvaluation

/-- The original supported-to-acyclic equivalence with the actual common-universe lifting. -/
def boundedAboveFlatAffineSupportedSectionAcyclicSmallEquivalence :
    BoundedAboveFlatAffineSupportedSections j ≌
      AsSmall.{0} (AcyclicCategory (boundedAboveFlatPerfectOpenNested j)) :=
  (boundedAboveFlatAffineSupportedSectionAcyclicEquivalence j).trans AsSmall.equiv

/-- The actual forward common-universe evaluation is exact. -/
theorem boundedAboveFlatAffineSupportedSectionAcyclicSmallEquivalence_exact :
    IsExact (boundedAboveFlatAffineSupportedSectionWaldhausen j).cof
      (boundedAboveFlatAffineSupportedSectionWaldhausen j).weq
      (acyclicStructure (boundedAboveFlatPerfectOpenNested j)).asSmall.cof
      (acyclicStructure (boundedAboveFlatPerfectOpenNested j)).asSmall.weq
      (boundedAboveFlatAffineSupportedSectionAcyclicSmallEquivalence j).functor := by
  change IsExact _ _ _ _ (boundedAboveFlatAffineSupportedSectionAcyclicEvaluation j ⋙ AsSmall.up)
  exact (boundedAboveFlatAffineSupportedSectionAcyclicEvaluation_exact j).comp
    (acyclicStructure (boundedAboveFlatPerfectOpenNested j)).asSmall_up_exact

/-- The unchanged actual inverse is exact for the same original inherited fine classes. -/
theorem boundedAboveFlatAffineSupportedSectionAcyclicSmallEquivalence_inverse_exact :
    IsExact (acyclicStructure (boundedAboveFlatPerfectOpenNested j)).asSmall.cof
      (acyclicStructure (boundedAboveFlatPerfectOpenNested j)).asSmall.weq
      (boundedAboveFlatAffineSupportedSectionWaldhausen j).cof
      (boundedAboveFlatAffineSupportedSectionWaldhausen j).weq
      (boundedAboveFlatAffineSupportedSectionAcyclicSmallEquivalence j).inverse :=
  (acyclicStructure (boundedAboveFlatPerfectOpenNested j)).asSmall_down_exact.comp
    (boundedAboveFlatAffineSupportedSectionAcyclicEquivalence_inverse_exact j)

/-- The actual supported evaluation retains the inherited geometric acyclic zero literally. -/
def boundedAboveFlatAffineSupportedSectionAcyclicModelMap :
    boundedAboveFlatAffineSupportedSectionModel j ⟶
      asSmallCategory (acyclicStructure (boundedAboveFlatPerfectOpenNested j)) :=
  ⟨⟨(boundedAboveFlatAffineSupportedSectionAcyclicSmallEquivalence j).functor,
    boundedAboveFlatAffineSupportedSectionAcyclicSmallEquivalence_exact j⟩,
    congrArg AsSmall.up.obj (boundedAboveFlatAffineSupportedSectionAcyclicEvaluation_zero j)⟩

/-- The same forward Model arrow induces the actual original supported-acyclic prespectrum map. -/
def boundedAboveFlatAffineSupportedSectionAcyclicPrespectrumMap :
    prespectrum (boundedAboveFlatAffineSupportedSectionModel j) ⟶
      originalPrespectrum (acyclicStructure (boundedAboveFlatPerfectOpenNested j)) :=
  prespectrumMap (boundedAboveFlatAffineSupportedSectionAcyclicModelMap j)

/-- The two unchanged original support-inclusion routes agree as actual Model arrows. -/
theorem boundedAboveFlatAffineSupportedSectionAcyclicModelMap_inclusion :
    boundedAboveFlatAffineSupportedSectionForgetModelMap j ≫
        boundedAboveFlatAffineEvaluationModelMap R =
      boundedAboveFlatAffineSupportedSectionAcyclicModelMap j ≫
        asSmallCategoryMap _ _ (acyclicInclusion_exact (boundedAboveFlatPerfectOpenNested
          j)) rfl := by
  apply WideSubcategory.hom_ext
  apply SmallWaldhausenCategory.Hom.ext
  exact asSmallFunctor_square (boundedAboveFlatAffineSectionSupported j).ι
    (boundedAboveFlatAffineOriginalEvaluation R)
      (boundedAboveFlatAffineSupportedSectionAcyclicEvaluation j)
    (acyclicInclusion (boundedAboveFlatPerfectOpenNested j))
    (boundedAboveFlatAffineSupportedSectionAcyclicEvaluation_inclusion j).symm

/-- The literal original inclusion square survives unchanged on actual prespectra. -/
theorem boundedAboveFlatAffineSupportedSectionAcyclicPrespectrumMap_inclusion :
    boundedAboveFlatAffineSupportedSectionForgetPrespectrumMap j ≫
        boundedAboveFlatAffineEvaluationPrespectrumMap R =
      boundedAboveFlatAffineSupportedSectionAcyclicPrespectrumMap j ≫
        acyclicInclusionPrespectrumMap (boundedAboveFlatPerfectOpenNested j) := by
  exact (prespectrumFunctor.map_comp _ _).symm.trans
    ((congrArg prespectrumFunctor.map
      (boundedAboveFlatAffineSupportedSectionAcyclicModelMap_inclusion j)).trans
        (prespectrumFunctor.map_comp _ _))

/-- Every original level map is a complete weak equivalence, including every component. -/
theorem boundedAboveFlatAffineSupportedSectionAcyclic_level_isWeakHomotopyEquivalence (n : ℕ) :
    IsWeakHomotopyEquivalence
      ((boundedAboveFlatAffineSupportedSectionAcyclicPrespectrumMap j).map n) :=
  ExactModelEquivalence.level_isWeakHomotopyEquivalence
    (V := boundedAboveFlatAffineSupportedSectionModel j)
    (W := asSmallCategory (acyclicStructure (boundedAboveFlatPerfectOpenNested j)))
    (boundedAboveFlatAffineSupportedSectionAcyclicSmallEquivalence j)
    (boundedAboveFlatAffineSupportedSectionAcyclicSmallEquivalence_exact j)
    (boundedAboveFlatAffineSupportedSectionAcyclicSmallEquivalence_inverse_exact j)
    (boundedAboveFlatAffineSupportedSectionAcyclicModelMap j).property n

/-- The same original supported-acyclic comparison is stable in every signed degree. -/
theorem boundedAboveFlatAffineSupportedSectionAcyclic_isStableEquivalence :
    LoopPrespectrum.IsStableEquivalence
      (boundedAboveFlatAffineSupportedSectionAcyclicPrespectrumMap j) :=
  ExactModelEquivalence.isStableEquivalence
    (V := boundedAboveFlatAffineSupportedSectionModel j)
    (W := asSmallCategory (acyclicStructure (boundedAboveFlatPerfectOpenNested j)))
    (boundedAboveFlatAffineSupportedSectionAcyclicSmallEquivalence j)
    (boundedAboveFlatAffineSupportedSectionAcyclicSmallEquivalence_exact j)
    (boundedAboveFlatAffineSupportedSectionAcyclicSmallEquivalence_inverse_exact j)
    (boundedAboveFlatAffineSupportedSectionAcyclicModelMap j).property

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    SupportedSectionAcyclicComparison.lean:35-122"
  "adaptation" "Actual supported-section comparison with its specified entire null track"]
  boundedAboveFlatAffineSupportedSectionAcyclicSmallEquivalence
  boundedAboveFlatAffineSupportedSectionAcyclicSmallEquivalence_exact
  boundedAboveFlatAffineSupportedSectionAcyclicSmallEquivalence_inverse_exact
  boundedAboveFlatAffineSupportedSectionAcyclicModelMap
  boundedAboveFlatAffineSupportedSectionAcyclicPrespectrumMap
  boundedAboveFlatAffineSupportedSectionAcyclicModelMap_inclusion
  boundedAboveFlatAffineSupportedSectionAcyclicPrespectrumMap_inclusion
  boundedAboveFlatAffineSupportedSectionAcyclic_level_isWeakHomotopyEquivalence
  boundedAboveFlatAffineSupportedSectionAcyclic_isStableEquivalence

end AlgebraicGeometry.Scheme.Modules
