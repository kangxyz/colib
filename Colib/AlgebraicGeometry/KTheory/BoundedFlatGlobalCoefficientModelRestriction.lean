/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSectionPrespectrum
public import Colib.AlgebraicGeometry.Modules.BoundedFlatGlobalCoefficientRestriction
public import Colib.CategoryTheory.Waldhausen.CocartesianSectionRestriction

/-!
# Exact global-to-joint coefficient section restriction

The actual raw restriction is exact and preserves the shared chosen zero literally. Its
categorical inverse is exact for the same evaluation-transported structures. These are the
original GlobalSectionChangeIndex and GlobalSectionChangeIndexLaws constructions at Quillen
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, on the existing native Waldhausen category.
No finite Bass-iterate stability or TT localization result is asserted here.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen AlgebraicGeometry
open CategoryTheory.Waldhausen.CocartesianSectionStructure
open AlgebraicGeometry.Scheme.BaseChange AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The actual global restriction is a strictly natural exact map with the same chosen zeros. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSectionChangeIndex.lean:60-66"
  "adaptation" "The unchanged coefficient restriction as a native strict Waldhausen map"]
def boundedAboveFlatGlobalCoefficientModelRestriction (R : CommRingCat.{u}) :
    Coefficients.functor R ⋙ boundedAboveFlatGlobalSectionModelFunctor ⟶
      boundedAboveFlatCoefficientSectionModelFunctor R :=
  restrictionModel boundedAboveFlatPerfectPseudofunctor boundedAboveFlatGlobalFiberWaldhausen
    boundedAboveFlatGlobalFiberZero boundedAboveFlatGlobalFiberZero_isZero
    (fun {_ _} f => boundedAboveFlatGlobalFiberZero_map_isZero f) (Coefficients.functor R)
    (fun {_ _} f => boundedAboveFlatGlobalFiber_exact f)

/-- The strict map has exactly the already constructed raw restriction as underlying functor. -/
theorem boundedAboveFlatGlobalCoefficientModelRestriction_toFunctor (R : CommRingCat.{u})
    (i : Index R) :
    ((boundedAboveFlatGlobalCoefficientModelRestriction R).app i).hom.toFunctor =
      boundedAboveFlatGlobalCoefficientRestriction R i := rfl

/-- Identity evaluation after the strict component is literally original global evaluation. -/
theorem boundedAboveFlatGlobalCoefficientModelRestriction_evaluation (R : CommRingCat.{u})
    (i : Index R) :
    ((boundedAboveFlatGlobalCoefficientModelRestriction R).app i).hom.toFunctor ⋙
        boundedAboveFlatCoefficientOriginalEvaluation i =
      boundedAboveFlatGlobalSectionEvaluation ((Coefficients.functor R).obj i) :=
  boundedAboveFlatGlobalCoefficientRestriction_evaluation R i

/-- The actual strict restriction component remains the original categorical equivalence. -/
instance boundedAboveFlatGlobalCoefficientModelRestriction_isEquivalence (R : CommRingCat.{u})
    (i : Index R) :
    (((boundedAboveFlatGlobalCoefficientModelRestriction R).app i).hom.toFunctor).IsEquivalence :=
  boundedAboveFlatGlobalCoefficientRestriction_isEquivalence R i

/-- The original raw restriction preserves the transported Waldhausen classes and pushouts. -/
theorem boundedAboveFlatGlobalCoefficientRestriction_exact (R : CommRingCat.{u}) (i : Index R) :
    Waldhausen.IsExact
      (boundedAboveFlatGlobalSectionWaldhausen ((Coefficients.functor R).obj i)).cof
      (boundedAboveFlatGlobalSectionWaldhausen ((Coefficients.functor R).obj i)).weq
      (boundedAboveFlatCoefficientSectionWaldhausen i).cof
      (boundedAboveFlatCoefficientSectionWaldhausen i).weq
      (boundedAboveFlatGlobalCoefficientRestriction R i) :=
  ((boundedAboveFlatGlobalCoefficientModelRestriction R).app i).hom.isExact

/-- The inverse of the actual categorical restriction is exact for those same structures. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSectionChangeIndexLaws.lean:49"
  "adaptation" "Original inverse exactness through the genuine evaluation equivalence"]
theorem boundedAboveFlatGlobalCoefficientRestriction_inverse_exact (R : CommRingCat.{u})
    (i : Index R) :
    Waldhausen.IsExact (boundedAboveFlatCoefficientSectionWaldhausen i).cof
      (boundedAboveFlatCoefficientSectionWaldhausen i).weq
      (boundedAboveFlatGlobalSectionWaldhausen ((Coefficients.functor R).obj i)).cof
      (boundedAboveFlatGlobalSectionWaldhausen ((Coefficients.functor R).obj i)).weq
      (boundedAboveFlatGlobalCoefficientRestriction R i).asEquivalence.inverse :=
  restriction_inverse_exact boundedAboveFlatPerfectPseudofunctor
    boundedAboveFlatGlobalFiberWaldhausen boundedAboveFlatGlobalFiberZero
    boundedAboveFlatGlobalFiberZero_isZero
    (fun {_ _} f => boundedAboveFlatGlobalFiberZero_map_isZero f) (Coefficients.functor R) i

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0538"] boundedAboveFlatGlobalCoefficientModelRestriction
attribute [colib_tag "COL-0538"] boundedAboveFlatGlobalCoefficientRestriction_inverse_exact

end AlgebraicGeometry.Scheme.Modules
