/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatGlobalSectionUnit
public import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientSections
public import Colib.CategoryTheory.FiberedCategory.SectionChangeIndexZero
public import Colib.CategoryTheory.FiberedCategory.SectionChangeIndexUnit

/-!
# Global section restriction to the joint scheme and coefficient index

Restriction is the original functor along the actual scheme/coefficient base-change family.
Identity evaluation remains equality, not an unspecified comparison. The target zero restricts
exactly the same global geometric zero family. No Bass-iterate or spectrum conclusion is asserted.

The underlying restriction and its evaluation/equivalence/zero laws are extracted from
`GlobalSectionChangeIndex.lean`, `GlobalSectionChangeIndexLaws.lean`,
`SectionChangeIndexMixedModel.lean` and `SectionChangeIndexZero.lean` in Quillen at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.GrothendieckZeroSections
open AlgebraicGeometry.Scheme.BaseChange AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The original joint section zero restricts the same global geometric zero family. -/
def boundedAboveFlatCoefficientSectionZero {R : CommRingCat.{u}} (i : Index R) :
    BoundedAboveFlatCoefficientSections i :=
  sectionZero (boundedAboveFlatCoefficientPseudofunctor R)
    (fun i => boundedAboveFlatGlobalFiberZero ((Coefficients.functor R).obj i))
    (fun i => boundedAboveFlatGlobalFiberZero_isZero ((Coefficients.functor R).obj i))
    (fun {_ _} f => boundedAboveFlatGlobalFiberZero_map_isZero ((Coefficients.functor R).map f)) i

/-- Restriction is the actual functor along the complete joint coefficient family. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSectionChangeIndexLaws.lean:29-33"
  "adaptation" "The underlying original restriction functor, before Waldhausen model bundling"]
def boundedAboveFlatGlobalCoefficientRestriction (R : CommRingCat.{u}) (i : Index R) :
    BoundedAboveFlatGlobalSections ((Coefficients.functor R).obj i) ⥤
      BoundedAboveFlatCoefficientSections i :=
  SectionChangeIndex.underFunctor boundedAboveFlatPerfectPseudofunctor (Coefficients.functor R) i

/-- Original identity evaluation after restriction is literally the same global evaluation. -/
theorem boundedAboveFlatGlobalCoefficientRestriction_evaluation (R : CommRingCat.{u})
    (i : Index R) :
    boundedAboveFlatGlobalCoefficientRestriction R i ⋙
        boundedAboveFlatCoefficientOriginalEvaluation i =
      boundedAboveFlatGlobalSectionEvaluation ((Coefficients.functor R).obj i) :=
  SectionChangeIndex.evaluation boundedAboveFlatPerfectPseudofunctor (Coefficients.functor R) i

/-- Restriction is an equivalence because both unchanged identity evaluations are equivalences. -/
instance boundedAboveFlatGlobalCoefficientRestriction_isEquivalence (R : CommRingCat.{u})
    (i : Index R) : (boundedAboveFlatGlobalCoefficientRestriction R i).IsEquivalence :=
  SectionChangeIndex.restriction_isEquivalence boundedAboveFlatPerfectPseudofunctor
    (Coefficients.functor R) i

/-- The actual restriction preserves the same geometric chosen-zero section by equality. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/FiberedCategory/SectionChangeIndexZero.lean:29-41"
  "adaptation" "Actual joint restriction retains the original global chosen zero literally"]
theorem boundedAboveFlatGlobalCoefficientRestriction_zero (R : CommRingCat.{u}) (i : Index R) :
    (boundedAboveFlatGlobalCoefficientRestriction R i).obj
        (boundedAboveFlatGlobalSectionZero ((Coefficients.functor R).obj i)) =
      boundedAboveFlatCoefficientSectionZero i :=
  SectionChangeIndex.restriction_sectionZero boundedAboveFlatPerfectPseudofunctor
    (Coefficients.functor R) boundedAboveFlatGlobalFiberZero boundedAboveFlatGlobalFiberZero_isZero
    (fun {_ _} f => boundedAboveFlatGlobalFiberZero_map_isZero f) i

/-- Restriction and both actual index directions commute as equality of the original functors. -/
theorem boundedAboveFlatGlobalCoefficientRestriction_naturality {R : CommRingCat.{u}}
    {i k : Index R} (f : i ⟶ k) :
    boundedAboveFlatGlobalSectionsMap ((Coefficients.functor R).map f) ⋙
        boundedAboveFlatGlobalCoefficientRestriction R k =
      boundedAboveFlatGlobalCoefficientRestriction R i ⋙ boundedAboveFlatCoefficientSectionsMap f :=
  SectionChangeIndex.reindex_naturality boundedAboveFlatPerfectPseudofunctor
    (Coefficients.functor R) f

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0535"] boundedAboveFlatGlobalCoefficientRestriction
attribute [colib_tag "COL-0535"] boundedAboveFlatGlobalCoefficientRestriction_evaluation
attribute [colib_tag "COL-0535"] boundedAboveFlatGlobalCoefficientRestriction_zero
attribute [colib_tag "COL-0535"] boundedAboveFlatGlobalCoefficientRestriction_naturality

end AlgebraicGeometry.Scheme.Modules
