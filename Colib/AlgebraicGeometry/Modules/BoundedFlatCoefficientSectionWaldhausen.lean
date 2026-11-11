/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientSectionZero
public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.ExactTransport

/-!
# Waldhausen structure on the joint coefficient sections

The existing geometric Waldhausen structure is transported through original identity evaluation.
The chosen zero is the same relocated global section zero, not an independently normalized one.
Exactness of reindexing uses the actual evaluation transition and geometric pullback, as in
`Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSections.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}}

/-- The original fiber Waldhausen classes and pushouts, with the same actual joint zero. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSections.lean:107"
  "adaptation" "Original evaluation-transported structure, exact maps and shared chosen zero"]
def boundedAboveFlatCoefficientSectionWaldhausen (i : Index R) :
    Waldhausen.Structure (BoundedAboveFlatCoefficientSections i) :=
  (boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace).ofEquivalence
    (boundedAboveFlatCoefficientSectionEquivalence i) (boundedAboveFlatCoefficientSectionZero i) (by
      change IsZero ((boundedAboveFlatCoefficientOriginalEvaluation i).obj
        (boundedAboveFlatCoefficientSectionZero i))
      rw [boundedAboveFlatCoefficientOriginalEvaluation_sectionZero]
      exact (boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace).isZero)

/-- The original chosen Waldhausen zero is the same restricted joint zero section. -/
theorem boundedAboveFlatCoefficientSectionWaldhausen_zero (i : Index R) :
    (boundedAboveFlatCoefficientSectionWaldhausen i).zero =
      boundedAboveFlatCoefficientSectionZero i := rfl

/-- Cofibrations are exactly those of the original identity-evaluated fiber map. -/
theorem boundedAboveFlatCoefficientSectionWaldhausen_cof_iff (i : Index R)
    {S T : BoundedAboveFlatCoefficientSections i} (f : S ⟶ T) :
    (boundedAboveFlatCoefficientSectionWaldhausen i).cof f ↔
      (boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace).cof
        ((boundedAboveFlatCoefficientOriginalEvaluation i).map f) := Iff.rfl

/-- Weak equivalences are exactly those of the original identity-evaluated fiber map. -/
theorem boundedAboveFlatCoefficientSectionWaldhausen_weq_iff (i : Index R)
    {S T : BoundedAboveFlatCoefficientSections i} (f : S ⟶ T) :
    (boundedAboveFlatCoefficientSectionWaldhausen i).weq f ↔
      (boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace).weq
        ((boundedAboveFlatCoefficientOriginalEvaluation i).map f) := Iff.rfl

/-- Original identity evaluation is exact for these transported original classes. -/
theorem boundedAboveFlatCoefficientOriginalEvaluation_exact (i : Index R) :
    Waldhausen.IsExact (boundedAboveFlatCoefficientSectionWaldhausen i).cof
      (boundedAboveFlatCoefficientSectionWaldhausen i).weq
      (boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace).weq
      (boundedAboveFlatCoefficientOriginalEvaluation i) :=
  Waldhausen.Structure.ofEquivalence_exact _ _ _ _

/-- The actual inverse evaluation equivalence is exact for the same original structures. -/
theorem boundedAboveFlatCoefficientSectionEquivalence_inverse_exact (i : Index R) :
    Waldhausen.IsExact (boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace).weq
      (boundedAboveFlatCoefficientSectionWaldhausen i).cof
      (boundedAboveFlatCoefficientSectionWaldhausen i).weq
      (boundedAboveFlatCoefficientSectionEquivalence i).inverse :=
  Waldhausen.Structure.ofEquivalence_inverse_exact _ _ _ _

/-- Reindexing followed by actual fiber evaluation is exact. -/
theorem boundedAboveFlatCoefficientSectionsMap_evaluation_exact {i k : Index R} (f : i ⟶ k) :
    Waldhausen.IsExact (boundedAboveFlatCoefficientSectionWaldhausen i).cof
      (boundedAboveFlatCoefficientSectionWaldhausen i).weq
      (boundedAboveFlatPerfectWaldhausen (space k).toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen (space k).toRingedSpace).weq
      (boundedAboveFlatCoefficientSectionsMap f ⋙
        boundedAboveFlatCoefficientOriginalEvaluation k) :=
  Waldhausen.ExtensionCategory.isExact_of_natIso
    (boundedAboveFlatCoefficientSectionWaldhausen i)
    (boundedAboveFlatPerfectWaldhausen (space k).toRingedSpace)
    ((boundedAboveFlatCoefficientOriginalEvaluation_exact i).comp
      (boundedAboveFlatPerfectPullback_isExact
        (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f)))
    (boundedAboveFlatCoefficientSectionReindexIso f).symm

/-- Original joint reindexing preserves zero, cofibrations, weak maps and pushouts. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSections.lean:164"
  "adaptation" "Original evaluation-transported structure, exact maps and shared chosen zero"]
theorem boundedAboveFlatCoefficientSectionsMap_exact {i k : Index R} (f : i ⟶ k) :
    Waldhausen.IsExact (boundedAboveFlatCoefficientSectionWaldhausen i).cof
      (boundedAboveFlatCoefficientSectionWaldhausen i).weq
      (boundedAboveFlatCoefficientSectionWaldhausen k).cof
      (boundedAboveFlatCoefficientSectionWaldhausen k).weq
      (boundedAboveFlatCoefficientSectionsMap f) where
  zero hx := IsZero.of_full_of_faithful_of_isZero
    (boundedAboveFlatCoefficientOriginalEvaluation k) _
    ((boundedAboveFlatCoefficientSectionsMap_evaluation_exact f).zero hx)
  cofibration g hg := (boundedAboveFlatCoefficientSectionsMap_evaluation_exact f).cofibration g hg
  weak g hg := (boundedAboveFlatCoefficientSectionsMap_evaluation_exact f).weak g hg
  pushout hi hp := by
    apply IsPushout.of_map_of_faithful (boundedAboveFlatCoefficientOriginalEvaluation k)
    exact (boundedAboveFlatCoefficientSectionsMap_evaluation_exact f).pushout hi hp

end AlgebraicGeometry.Scheme.Modules
