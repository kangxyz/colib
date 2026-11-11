/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionAcyclicComparison
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumZeroNaturality

/-!
# Evaluation of the original supported-section null track

The actual inherited-zero inclusion square transports the entire original weak
zero-to-section transformation. Its reversed homotopy agrees at every parameter with the
original geometric acyclic null track. No endpoint-only replacement or time change is used.
-/
@[expose] public section

open CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.Fibration
open CategoryTheory.Waldhausen.IteratedS

noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Modules
open CategoryTheory.Waldhausen.SmallWaldhausenCategory AlgebraicGeometry.RingedSpace Topology
open Waldhausen Waldhausen.Fibration Waldhausen.IteratedS
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
attribute [local irreducible] boundedAboveFlatAffineOriginalEvaluation
  boundedAboveFlatAffineSupportedSectionEquivalence boundedAboveFlatAffineSupportedEvaluation

/-- Original evaluation preserves every value of the unchanged support-restriction null track. -/
theorem boundedAboveFlatAffineSupportedSectionOpenNullHomotopy_evaluation (n : ℕ) (s : unitInterval)
    (x : (prespectrum (boundedAboveFlatAffineSupportedSectionModel j)).space n) :
    (boundedAboveFlatAffineSectionOpenEvaluationPrespectrumMap j).map n
        ((boundedAboveFlatAffineSupportedSectionOpenNullHomotopy j).level n (s, x)) =
      (acyclicPrespectrumNullhomotopy (boundedAboveFlatPerfectOpenNested j)).level n
        (s, (boundedAboveFlatAffineSupportedSectionAcyclicPrespectrumMap j).map n x) := by
  let N := boundedAboveFlatPerfectOpenNested j
  let F := boundedAboveFlatAffineSupportedSectionForgetModelMap j ≫
    boundedAboveFlatAffineSectionOpenModelMap j
  let G := asSmallCategoryMap (acyclicStructure N) N.coarse (acyclicInclusion_coarse_exact N)
    (by simpa only [acyclicInclusion_zero] using N.coarse_zero.symm)
  let a := boundedAboveFlatAffineSupportedSectionAcyclicModelMap j
  let b := boundedAboveFlatAffineSectionOpenEvaluationModelMap j
  have hs : F ≫ b = a ≫ G := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    apply asSmallFunctor_square F.hom.toFunctor (boundedAboveFlatAffineOriginalEvaluation R)
      (boundedAboveFlatAffineSupportedSectionAcyclicEvaluation j) (acyclicInclusion N)
    exact (congrArg (fun K => K ⋙ boundedAboveFlatAffineOriginalEvaluation R)
      (CategoryTheory.Functor.comp_id (boundedAboveFlatAffineSectionSupported j).ι)).trans
        (boundedAboveFlatAffineSupportedSectionAcyclicEvaluation_inclusion j).symm
  let θ : (zeroHom (asSmallCategory (acyclicStructure N)) (asSmallCategory
    N.coarse)).hom.toFunctor ⟶ G.hom.toFunctor :=
    whiskerLeft AsSmall.down (whiskerRight (zeroToAcyclicInclusion N) AsSmall.up)
  have hθ : ∀ A, (asSmallCategory N.coarse).obj.waldhausen.weq (θ.app A) :=
    fun A => zeroToAcyclicInclusion_weak N (AsSmall.down.obj A)
  have h := prespectrumZeroTransformationHomotopy_naturality F G a b hs
    (boundedAboveFlatAffineSupportedSectionZeroToOpen j) θ
    (boundedAboveFlatAffineSupportedSectionZeroToOpen_weak j) hθ n
  exact congrArg (fun H => H (unitInterval.symm s, x)) h

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    SupportedSectionOpenNullNaturality.lean:35-63"
  "adaptation" "Actual supported-section comparison with its specified entire null track"]
  boundedAboveFlatAffineSupportedSectionOpenNullHomotopy_evaluation

end AlgebraicGeometry.Scheme.Modules
