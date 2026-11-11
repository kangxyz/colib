/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionForgetExact
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectOpenSupport

/-!
# Original supported section evaluation into relative acyclics

The original supported evaluation is followed by the proved geometric support-to-acyclic
functor. Its forward and inverse are genuinely exact, and the original section zero maps to
the inherited fine geometric zero. This retains the literal support inclusion for subsequent
null-track comparison without identifying independently chosen supported geometric zeros.
-/
@[expose] public section

open CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.Fibration

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RingedSpace Topology
universe u
namespace AlgebraicGeometry.Scheme.Modules
open Waldhausen Waldhausen.Fibration
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
attribute [local irreducible] boundedAboveFlatAffineOriginalEvaluation
  boundedAboveFlatAffineSupportedSectionEquivalence boundedAboveFlatAffineSupportedEvaluation

/-- Original supported evaluation followed by the actual support-to-acyclic conversion. -/
def boundedAboveFlatAffineSupportedSectionAcyclicEvaluation :
    BoundedAboveFlatAffineSupportedSections j ⥤ AcyclicCategory
      (boundedAboveFlatPerfectOpenNested j) :=
  boundedAboveFlatAffineSupportedEvaluation j ⋙ boundedAboveFlatPerfectSupportedToAcyclic j

/-- The same actual supported functor is exact for the inherited fine classes. -/
theorem boundedAboveFlatAffineSupportedSectionAcyclicEvaluation_exact :
    IsExact (boundedAboveFlatAffineSupportedSectionWaldhausen j).cof
      (boundedAboveFlatAffineSupportedSectionWaldhausen j).weq
      (acyclicStructure (boundedAboveFlatPerfectOpenNested j)).cof
      (acyclicStructure (boundedAboveFlatPerfectOpenNested j)).weq
      (boundedAboveFlatAffineSupportedSectionAcyclicEvaluation j) :=
  (boundedAboveFlatAffineSupportedEvaluation_exact j).comp
    (boundedAboveFlatPerfectSupportedToAcyclic_exact j)

/-- Forgetting actual acyclicity retains the original support inclusion/evaluation composite. -/
theorem boundedAboveFlatAffineSupportedSectionAcyclicEvaluation_inclusion :
    boundedAboveFlatAffineSupportedSectionAcyclicEvaluation j ⋙
        acyclicInclusion (boundedAboveFlatPerfectOpenNested j) =
      (boundedAboveFlatAffineSectionSupported j).ι ⋙
        boundedAboveFlatAffineOriginalEvaluation R := by
  rw [boundedAboveFlatAffineSupportedSectionAcyclicEvaluation, Functor.assoc,
    boundedAboveFlatPerfectSupportedToAcyclic_comp_inclusion,
    boundedAboveFlatAffineSupportedEvaluation_forget_to_boundedFlat]

/-- The genuine categorical equivalence keeps this exact original composite as forward functor. -/
def boundedAboveFlatAffineSupportedSectionAcyclicEquivalence :
    BoundedAboveFlatAffineSupportedSections j ≌ AcyclicCategory
      (boundedAboveFlatPerfectOpenNested j) :=
  ((boundedAboveFlatAffineSupportedSectionEquivalence j).trans
    (boundedAboveFlatPerfectAcyclicSupportedEquivalence j).symm).changeFunctor
      (eqToIso (congrArg (fun F => F ⋙ boundedAboveFlatPerfectSupportedToAcyclic j)
        (boundedAboveFlatAffineSupportedSectionEquivalence_functor j)))

/-- Its original inverse retains the proved two fine exact inverses. -/
theorem boundedAboveFlatAffineSupportedSectionAcyclicEquivalence_inverse_exact :
    IsExact (acyclicStructure (boundedAboveFlatPerfectOpenNested j)).cof
      (acyclicStructure (boundedAboveFlatPerfectOpenNested j)).weq
      (boundedAboveFlatAffineSupportedSectionWaldhausen j).cof
      (boundedAboveFlatAffineSupportedSectionWaldhausen j).weq
      (boundedAboveFlatAffineSupportedSectionAcyclicEquivalence j).inverse :=
  (boundedAboveFlatPerfectAcyclicToSupported_exact j).comp
    (boundedAboveFlatAffineSupportedSectionEquivalence_inverse_exact j)

/-- The inherited acyclic zero is the actual image of the original supported section zero. -/
theorem boundedAboveFlatAffineSupportedSectionAcyclicEvaluation_zero :
    (boundedAboveFlatAffineSupportedSectionAcyclicEvaluation j).obj
        (boundedAboveFlatAffineSupportedSectionWaldhausen j).zero =
      (acyclicStructure (boundedAboveFlatPerfectOpenNested j)).zero := by
  apply ObjectProperty.FullSubcategory.ext
  have h := congrArg (fun F => F.obj (boundedAboveFlatAffineSupportedSectionWaldhausen j).zero)
    (boundedAboveFlatAffineSupportedSectionAcyclicEvaluation_inclusion j)
  refine h.trans ?_
  change (boundedAboveFlatAffineOriginalEvaluation R).obj
      ((boundedAboveFlatAffineSectionSupported j).ι.obj
        (boundedAboveFlatAffineSupportedSectionWaldhausen j).zero) =
    (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace).zero
  rw [boundedAboveFlatAffineSupportedSectionForget_zero,
    boundedAboveFlatAffineSectionWaldhausen_zero,
    boundedAboveFlatAffineOriginalEvaluation_sectionZero]

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    SupportedSectionAcyclicEvaluation.lean:34-86"
  "adaptation" "Actual inherited-zero evaluation, original maps and their complete comparison"]
  boundedAboveFlatAffineSupportedSectionAcyclicEvaluation
  boundedAboveFlatAffineSupportedSectionAcyclicEvaluation_exact
  boundedAboveFlatAffineSupportedSectionAcyclicEvaluation_inclusion
  boundedAboveFlatAffineSupportedSectionAcyclicEquivalence
  boundedAboveFlatAffineSupportedSectionAcyclicEquivalence_inverse_exact
  boundedAboveFlatAffineSupportedSectionAcyclicEvaluation_zero

end AlgebraicGeometry.Scheme.Modules
