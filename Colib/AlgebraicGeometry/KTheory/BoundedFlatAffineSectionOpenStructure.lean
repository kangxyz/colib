/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatAffineSectionWaldhausen
public import Colib.CategoryTheory.Waldhausen.Fibration.InverseImageWeak
public import Colib.CategoryTheory.Waldhausen.Fibration.ExactChangeWeak
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectOpen

/-!
# Original relative-open Waldhausen structure on affine sections

The original section category keeps its cofibrations and chosen zero. Weak equivalences
are detected by actual original evaluation into the existing bounded-flat relative-open
model. The original functor is retained by enlarging only its target weak class.
This construction makes no assertion about the full open K₀ endpoint.
-/
@[expose] public section

open CategoryTheory.Waldhausen

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace AlgebraicGeometry.Scheme.Modules
open Waldhausen Fibration
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
attribute [local irreducible] boundedAboveFlatAffineOriginalEvaluation

/-- Original evaluation is exact into the original geometric relative-open structure. -/
theorem boundedAboveFlatAffineSectionOpenEvaluation_exact :
    IsExact (boundedAboveFlatAffineSectionWaldhausen R).cof
      (boundedAboveFlatAffineSectionWaldhausen R).weq
      (boundedAboveFlatPerfectOpenWaldhausen j).cof (boundedAboveFlatPerfectOpenWaldhausen j).weq
      (boundedAboveFlatAffineOriginalEvaluation R) :=
  (boundedAboveFlatAffineOriginalEvaluation_exact R).changeWeakTarget
    (boundedAboveFlatPerfectOpenNested j)

/-- Actual relative-open weakness, retaining the original section cofibrations and zero. -/
def boundedAboveFlatAffineSectionOpenWaldhausen : Structure (BoundedAboveFlatAffineSections R) :=
  Structure.withInverseImageWeak (boundedAboveFlatAffineSectionOpenEvaluation_exact j)

/-- The unchanged fine section weak class lies in the actual relative-open weak class. -/
def boundedAboveFlatAffineSectionOpenNested :
    NestedWeakEquivalences (boundedAboveFlatAffineSectionWaldhausen R) :=
  Structure.inverseImageWeakNested (boundedAboveFlatAffineSectionOpenEvaluation_exact j)

/-- Evaluation preserves the new genuine coarse weak class by its defining original map. -/
theorem boundedAboveFlatAffineSectionOpenEvaluation_coarse_exact :
    IsExact (boundedAboveFlatAffineSectionOpenWaldhausen j).cof
      (boundedAboveFlatAffineSectionOpenWaldhausen j).weq
      (boundedAboveFlatPerfectOpenWaldhausen j).cof (boundedAboveFlatPerfectOpenWaldhausen j).weq
      (boundedAboveFlatAffineOriginalEvaluation R) :=
  Structure.withInverseImageWeak_exact (boundedAboveFlatAffineSectionOpenEvaluation_exact j)

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SectionOpenStructure.lean:35-58"
  "adaptation" "Actual relative-open section construction with the original maps and weak class"]
  boundedAboveFlatAffineSectionOpenEvaluation_exact
  boundedAboveFlatAffineSectionOpenWaldhausen
  boundedAboveFlatAffineSectionOpenNested
  boundedAboveFlatAffineSectionOpenEvaluation_coarse_exact

end AlgebraicGeometry.Scheme.Modules
