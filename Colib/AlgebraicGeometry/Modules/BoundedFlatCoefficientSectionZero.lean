/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors, kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatGlobalSections
public import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientSections

/-!
# The same chosen zero on joint coefficient sections

The chosen-zero declaration is relocated unchanged from the original global restriction owner.
It restricts the same global geometric zero family. Evaluation and reindexing keep that zero
literally; no second zero is selected. The laws are the original CoefficientSections zero laws
at Quillen `c561118b7795eb9780be9ed391c3251d6a4d0afd`, on the existing native section objects.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RingedSpace
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

/-- The restricted global zero has the original universal property. -/
theorem boundedAboveFlatCoefficientSectionZero_isZero {R : CommRingCat.{u}} (i : Index R) :
    IsZero (boundedAboveFlatCoefficientSectionZero i) :=
  isZero_sectionZero (boundedAboveFlatCoefficientPseudofunctor R)
    (fun i => boundedAboveFlatGlobalFiberZero ((Coefficients.functor R).obj i))
    (fun i => boundedAboveFlatGlobalFiberZero_isZero ((Coefficients.functor R).obj i))
    (fun {_ _} f => boundedAboveFlatGlobalFiberZero_map_isZero ((Coefficients.functor R).map f)) i

/-- Original evaluation keeps exactly the original native geometric zero. -/
theorem boundedAboveFlatCoefficientOriginalEvaluation_sectionZero {R : CommRingCat.{u}}
    (i : Index R) :
    (boundedAboveFlatCoefficientOriginalEvaluation i).obj
        (boundedAboveFlatCoefficientSectionZero i) =
      (boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace).zero := rfl

/-- Actual joint reindexing preserves the restriction of the same global zero family. -/
theorem boundedAboveFlatCoefficientSectionsMap_sectionZero {R : CommRingCat.{u}}
    {i k : Index R} (f : i ⟶ k) :
    (boundedAboveFlatCoefficientSectionsMap f).obj (boundedAboveFlatCoefficientSectionZero i) =
      boundedAboveFlatCoefficientSectionZero k :=
  reindex_sectionZero (boundedAboveFlatCoefficientPseudofunctor R)
    (fun i => boundedAboveFlatGlobalFiberZero ((Coefficients.functor R).obj i))
    (fun i => boundedAboveFlatGlobalFiberZero_isZero ((Coefficients.functor R).obj i))
    (fun {_ _} g => boundedAboveFlatGlobalFiberZero_map_isZero ((Coefficients.functor R).map g)) f

end AlgebraicGeometry.Scheme.Modules
