/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionOpenEquivalence
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionOpenNull
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationComparison
public import Colib.KTheory.Waldhausen.Fibration.Prespectrum

/-!
# Actual relative-open section evaluation on prespectra

Original evaluation, followed by its original common-universe inclusion, is exact in both
directions for the genuine relative-open weak structures. Its original chosen section zero
maps to the inherited geometric zero by the already proved fine evaluation equality. The same
forward Model map has whole two-sided inverse homotopies and is a complete weak equivalence
at every level. No identification with the full open-scheme endpoint is asserted.
-/
@[expose] public section

open CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.IteratedS

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace Topology
universe u
namespace AlgebraicGeometry.Scheme.Modules
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open Waldhausen Waldhausen.IteratedS
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
attribute [local irreducible] boundedAboveFlatAffineOriginalEvaluation

/-- The actual evaluation followed by original universe lifting preserves the relative classes. -/
theorem boundedAboveFlatAffineSectionOpenSmallEquivalence_exact :
    IsExact (boundedAboveFlatAffineSectionOpenWaldhausen j).cof
      (boundedAboveFlatAffineSectionOpenWaldhausen j).weq
      (boundedAboveFlatPerfectOpenWaldhausen j).asSmall.cof
      (boundedAboveFlatPerfectOpenWaldhausen j).asSmall.weq
      (boundedAboveFlatAffineEvaluationSmallEquivalence R).functor :=
  (boundedAboveFlatAffineSectionOpenEvaluation_coarse_exact j).comp
    (boundedAboveFlatPerfectOpenWaldhausen j).asSmall_up_exact

/-- The same original common-universe inverse is exact for the actual relative classes. -/
theorem boundedAboveFlatAffineSectionOpenSmallEquivalence_inverse_exact :
    IsExact (boundedAboveFlatPerfectOpenWaldhausen j).asSmall.cof
      (boundedAboveFlatPerfectOpenWaldhausen j).asSmall.weq
      (boundedAboveFlatAffineSectionOpenWaldhausen j).cof
      (boundedAboveFlatAffineSectionOpenWaldhausen j).weq
      (boundedAboveFlatAffineEvaluationSmallEquivalence R).inverse :=
  (boundedAboveFlatPerfectOpenWaldhausen j).asSmall_down_exact.comp
    (boundedAboveFlatAffineSectionOpenEquivalence_inverse_exact j)

/-- Original evaluation sends the unchanged section zero to the inherited geometric zero. -/
def boundedAboveFlatAffineSectionOpenEvaluationModelMap :
    boundedAboveFlatAffineSectionOpenModel j ⟶
      asSmallCategory (boundedAboveFlatPerfectOpenWaldhausen j) :=
  ⟨⟨(boundedAboveFlatAffineEvaluationSmallEquivalence R).functor,
    boundedAboveFlatAffineSectionOpenSmallEquivalence_exact j⟩,
    boundedAboveFlatAffineEvaluationSmall_zero R⟩

/-- The actual relative-open comparison retains the original evaluated section map. -/
def boundedAboveFlatAffineSectionOpenEvaluationPrespectrumMap :
    prespectrum (boundedAboveFlatAffineSectionOpenModel j) ⟶
      originalPrespectrum (boundedAboveFlatPerfectOpenWaldhausen j) :=
  prespectrumMap (boundedAboveFlatAffineSectionOpenEvaluationModelMap j)

/-- The actual fine/coarse square commutes for the unchanged section and geometric maps. -/
theorem boundedAboveFlatAffineSectionOpenEvaluation_changeWeak :
    boundedAboveFlatAffineSectionOpenPrespectrumMap j ≫
        boundedAboveFlatAffineSectionOpenEvaluationPrespectrumMap j =
      boundedAboveFlatAffineEvaluationPrespectrumMap R ≫
        Fibration.changeWeakPrespectrumMap (boundedAboveFlatPerfectOpenNested j) := by
  change prespectrumFunctor.map (boundedAboveFlatAffineSectionOpenModelMap j) ≫
      prespectrumFunctor.map (boundedAboveFlatAffineSectionOpenEvaluationModelMap j) =
    prespectrumFunctor.map (boundedAboveFlatAffineEvaluationModelMap R) ≫
      prespectrumFunctor.map (asSmallCategoryMap _ _
        (Fibration.changeWeak_exact (boundedAboveFlatPerfectOpenNested j))
        (boundedAboveFlatPerfectOpenNested j).zero_eq.symm)
  rw [← prespectrumFunctor.map_comp, ← prespectrumFunctor.map_comp]
  apply congrArg prespectrumFunctor.map
  apply WideSubcategory.hom_ext
  apply SmallWaldhausenCategory.Hom.ext
  change 𝟭 _ ⋙ (boundedAboveFlatAffineEvaluationSmallEquivalence R).functor =
    (boundedAboveFlatAffineEvaluationSmallEquivalence R).functor ⋙ 𝟭 _
  rw [Functor.id_comp, Functor.comp_id]

/-- The actual inverse uses only canonical chosen-zero normalization of evaluation's inverse. -/
def boundedAboveFlatAffineSectionOpenEvaluationInversePrespectrumMap :
    originalPrespectrum (boundedAboveFlatPerfectOpenWaldhausen j) ⟶
      prespectrum (boundedAboveFlatAffineSectionOpenModel j) :=
  prespectrumMap (ExactModelEquivalence.backward
    (V := boundedAboveFlatAffineSectionOpenModel j)
    (W := asSmallCategory (boundedAboveFlatPerfectOpenWaldhausen j))
    (boundedAboveFlatAffineEvaluationSmallEquivalence R)
    (boundedAboveFlatAffineSectionOpenSmallEquivalence_inverse_exact j))

/-- The original categorical unit and inverse normalization give a whole left inverse track. -/
def boundedAboveFlatAffineSectionOpenEvaluationLeftHomotopy : LoopPrespectrum.Homotopy
    (boundedAboveFlatAffineSectionOpenEvaluationPrespectrumMap j ≫
      boundedAboveFlatAffineSectionOpenEvaluationInversePrespectrumMap j)
    (𝟙 (prespectrum (boundedAboveFlatAffineSectionOpenModel j))) :=
  ExactModelEquivalence.leftHomotopy
    (V := boundedAboveFlatAffineSectionOpenModel j)
    (W := asSmallCategory (boundedAboveFlatPerfectOpenWaldhausen j))
    (boundedAboveFlatAffineEvaluationSmallEquivalence R)
    (boundedAboveFlatAffineSectionOpenSmallEquivalence_exact j)
    (boundedAboveFlatAffineSectionOpenSmallEquivalence_inverse_exact j)
    (boundedAboveFlatAffineEvaluationSmall_zero R)

/-- The unchanged categorical counit and the same normalization give the whole right track. -/
def boundedAboveFlatAffineSectionOpenEvaluationRightHomotopy : LoopPrespectrum.Homotopy
    (boundedAboveFlatAffineSectionOpenEvaluationInversePrespectrumMap j ≫
      boundedAboveFlatAffineSectionOpenEvaluationPrespectrumMap j)
    (𝟙 (originalPrespectrum (boundedAboveFlatPerfectOpenWaldhausen j))) :=
  ExactModelEquivalence.rightHomotopy
    (V := boundedAboveFlatAffineSectionOpenModel j)
    (W := asSmallCategory (boundedAboveFlatPerfectOpenWaldhausen j))
    (boundedAboveFlatAffineEvaluationSmallEquivalence R)
    (boundedAboveFlatAffineSectionOpenSmallEquivalence_exact j)
    (boundedAboveFlatAffineSectionOpenSmallEquivalence_inverse_exact j)
    (boundedAboveFlatAffineEvaluationSmall_zero R)

/-- Every level of the same original forward relative-open comparison is completely weak. -/
theorem boundedAboveFlatAffineSectionOpenEvaluation_level_isWeakHomotopyEquivalence (n : ℕ) :
    IsWeakHomotopyEquivalence ((boundedAboveFlatAffineSectionOpenEvaluationPrespectrumMap
      j).map n) :=
  ExactModelEquivalence.level_isWeakHomotopyEquivalence
    (V := boundedAboveFlatAffineSectionOpenModel j)
    (W := asSmallCategory (boundedAboveFlatPerfectOpenWaldhausen j))
    (boundedAboveFlatAffineEvaluationSmallEquivalence R)
    (boundedAboveFlatAffineSectionOpenSmallEquivalence_exact j)
    (boundedAboveFlatAffineSectionOpenSmallEquivalence_inverse_exact j)
    (boundedAboveFlatAffineEvaluationSmall_zero R) n

/-- The actual original relative-open evaluation is consequently stable in every signed degree. -/
theorem boundedAboveFlatAffineSectionOpenEvaluation_isStableEquivalence :
    LoopPrespectrum.IsStableEquivalence
      (boundedAboveFlatAffineSectionOpenEvaluationPrespectrumMap j) :=
  ExactModelEquivalence.isStableEquivalence
    (V := boundedAboveFlatAffineSectionOpenModel j)
    (W := asSmallCategory (boundedAboveFlatPerfectOpenWaldhausen j))
    (boundedAboveFlatAffineEvaluationSmallEquivalence R)
    (boundedAboveFlatAffineSectionOpenSmallEquivalence_exact j)
    (boundedAboveFlatAffineSectionOpenSmallEquivalence_inverse_exact j)
    (boundedAboveFlatAffineEvaluationSmall_zero R)

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SectionOpenComparison.lean:36-142"
  "adaptation" "Actual inherited-zero evaluation, original maps and their complete comparison"]
  boundedAboveFlatAffineSectionOpenSmallEquivalence_exact
  boundedAboveFlatAffineSectionOpenSmallEquivalence_inverse_exact
  boundedAboveFlatAffineSectionOpenEvaluationModelMap
  boundedAboveFlatAffineSectionOpenEvaluationPrespectrumMap
  boundedAboveFlatAffineSectionOpenEvaluation_changeWeak
  boundedAboveFlatAffineSectionOpenEvaluationInversePrespectrumMap
  boundedAboveFlatAffineSectionOpenEvaluationLeftHomotopy
  boundedAboveFlatAffineSectionOpenEvaluationRightHomotopy
  boundedAboveFlatAffineSectionOpenEvaluation_level_isWeakHomotopyEquivalence
  boundedAboveFlatAffineSectionOpenEvaluation_isStableEquivalence

end AlgebraicGeometry.Scheme.Modules
