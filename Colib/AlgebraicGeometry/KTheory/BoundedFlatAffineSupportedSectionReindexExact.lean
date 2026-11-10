/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedPullback
public import Colib.AlgebraicGeometry.Modules.BoundedFlatAffineSupportedSectionWaldhausen
public import Colib.AlgebraicGeometry.Modules.BoundedFlatAffineSupportedSectionCoefficientIso
public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.ExactTransport

/-!
# Original supported coefficient reindexing is Waldhausen-exact

The genuine geometric supported pullback and original evaluation comparison prove exactness
of the unchanged supported section reindexing. The existing actual evaluation equivalence
reflects zero objects and pushouts. Coefficient comparison remains a natural isomorphism;
no strict naturality of geometric evaluation or negative localization is inferred.
Adapted from Quillen `BoundedFlat/SupportedSectionReindexExact.lean:34-62` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R S : CommRingCat.{u}} {U V : Scheme.{u}}
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f)
attribute [local irreducible] boundedAboveFlatAffineOriginalEvaluation
  boundedAboveFlatAffineSupportedSectionEquivalence boundedAboveFlatAffineSupportedEvaluation

/-- The original reindexed evaluation is exact through its genuine geometric coefficient iso. -/
theorem boundedAboveFlatAffineSupportedSectionsMap_evaluation_exact :
    Waldhausen.IsExact (boundedAboveFlatAffineSupportedSectionWaldhausen j).cof
      (boundedAboveFlatAffineSupportedSectionWaldhausen j).weq
      (boundedAboveFlatPerfectSupportedWaldhausen j').cof
      (boundedAboveFlatPerfectSupportedWaldhausen j').weq
      (boundedAboveFlatAffineSupportedSectionsMap j j' f l h ⋙
        boundedAboveFlatAffineSupportedEvaluation j') :=
  Waldhausen.ExtensionCategory.isExact_of_natIso
    (boundedAboveFlatAffineSupportedSectionWaldhausen j)
    (boundedAboveFlatPerfectSupportedWaldhausen j')
    ((boundedAboveFlatAffineSupportedEvaluation_exact j).comp
      (boundedAboveFlatPerfectSupportedPullback_isExact
        (boundedAboveFlatAffineSupportedPairSquare j j' f l h)))
    (boundedAboveFlatAffineSupportedSectionCoefficientIso j j' f l h).symm

/-- Every unchanged supported coefficient map is exact, with its actual original open square. -/
theorem boundedAboveFlatAffineSupportedSectionsMap_exact :
    Waldhausen.IsExact (boundedAboveFlatAffineSupportedSectionWaldhausen j).cof
      (boundedAboveFlatAffineSupportedSectionWaldhausen j).weq
      (boundedAboveFlatAffineSupportedSectionWaldhausen j').cof
      (boundedAboveFlatAffineSupportedSectionWaldhausen j').weq
      (boundedAboveFlatAffineSupportedSectionsMap j j' f l h) where
  zero hx := IsZero.of_full_of_faithful_of_isZero (boundedAboveFlatAffineSupportedEvaluation j') _
    ((boundedAboveFlatAffineSupportedSectionsMap_evaluation_exact j j' f l h).zero hx)
  cofibration a ha := (boundedAboveFlatAffineSupportedSectionWaldhausen_cof_iff j' _).mpr
    ((boundedAboveFlatAffineSupportedSectionsMap_evaluation_exact j j' f l h).cofibration a ha)
  weak a ha := (boundedAboveFlatAffineSupportedSectionWaldhausen_weq_iff j' _).mpr
    ((boundedAboveFlatAffineSupportedSectionsMap_evaluation_exact j j' f l h).weak a ha)
  pushout hi hp := by
    apply IsPushout.of_map_of_faithful (boundedAboveFlatAffineSupportedEvaluation j')
    exact (boundedAboveFlatAffineSupportedSectionsMap_evaluation_exact j j' f l h).pushout hi hp

/-- Every original supported restriction preserves the existing chosen zero literally. -/
theorem boundedAboveFlatAffineSupportedSectionsMap_sectionZero :
    (boundedAboveFlatAffineSupportedSectionsMap j j' f l h).obj
        (boundedAboveFlatAffineSupportedSectionZero j) =
      boundedAboveFlatAffineSupportedSectionZero j' := by
  apply ObjectProperty.FullSubcategory.ext
  exact boundedAboveFlatAffineSectionsMap_sectionZero f

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0501", colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    SupportedSectionReindexExact.lean:34-62"
  "adaptation"
  "Exactness transported along the actual coefficient iso and reflected through supported \
    evaluation"]
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSupportedSectionsMap_evaluation_exact
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSupportedSectionsMap_exact

attribute [colib_tag "COL-0501", colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedSectionZero.lean:52-59"
  "adaptation" "Literal preservation of the existing pointwise supported zero section"]
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSupportedSectionsMap_sectionZero
