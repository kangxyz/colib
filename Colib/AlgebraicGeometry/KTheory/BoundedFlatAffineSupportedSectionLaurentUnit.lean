/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionUnitHomotopy
public import Colib.AlgebraicGeometry.Modules.BoundedFlatAffineSectionLaurentUnit
public import Colib.AlgebraicGeometry.Scheme.LaurentInclusionSquare

/-!
# The original Laurent coordinate on actual supported sections

Support restriction retains the full original forward and inverse Laurent section automorphisms.
The original target global-unit coordinate and inverse-coordinate formulas remain available from
the ambient owner. The direct, expanded equality on evaluated complex terms remains a separate
uncompleted proof. The original scalar coefficient equation supplies the supported action square,
and each specified original Laurent open-pair square has its genuine realized self-homotopy.
The fixed-open coefficient diagram is supplied by its separate diagram owner; constructing its
actual Bass seed remains separate.
-/
@[expose] public section


noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Waldhausen.IteratedS Topology
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R S : CommRingCat.{u}} {U V : Scheme.{u}}
attribute [local irreducible] boundedAboveFlatAffineOriginalEvaluation
  boundedAboveFlatAffineEvaluationAt
  boundedAboveFlatPerfectGlobalUnitIso

/-- The supported action is the original Laurent global unit, with no replacement scalar. -/
def boundedAboveFlatAffineSupportedSectionLaurentUnitIso
    (j : U ⟶ Spec (.of (LaurentPolynomial R))) [IsOpenImmersion j] :
    𝟭 (BoundedAboveFlatAffineSupportedSections j) ≅ 𝟭 (BoundedAboveFlatAffineSupportedSections j) :=
  boundedAboveFlatAffineSupportedSectionUnitIso j (laurentCoordinate R)

/-- Forgetting support retains the original forward Laurent automorphism on the entire section. -/
theorem boundedAboveFlatAffineSupportedSectionLaurentUnitIso_hom_original
    (j : U ⟶ Spec (.of (LaurentPolynomial R))) [IsOpenImmersion j]
    (s : BoundedAboveFlatAffineSupportedSections j) :
    ((boundedAboveFlatAffineSupportedSectionLaurentUnitIso j).hom.app s).hom =
      (boundedAboveFlatAffineSectionLaurentUnitIso R).hom.app s.obj :=
  boundedAboveFlatAffineSupportedSectionUnitIso_hom j (laurentCoordinate R) s

/-- Forgetting support also retains the unchanged inverse Laurent automorphism. -/
theorem boundedAboveFlatAffineSupportedSectionLaurentUnitIso_inv_original
    (j : U ⟶ Spec (.of (LaurentPolynomial R))) [IsOpenImmersion j]
    (s : BoundedAboveFlatAffineSupportedSections j) :
    ((boundedAboveFlatAffineSupportedSectionLaurentUnitIso j).inv.app s).hom =
      (boundedAboveFlatAffineSectionLaurentUnitIso R).inv.app s.obj :=
  boundedAboveFlatAffineSupportedSectionUnitIso_inv j (laurentCoordinate R) s

/-- Original Laurent coefficient maps preserve the exact supported target-unit action. -/
theorem boundedAboveFlatAffineSupportedSectionLaurentUnitIso_coefficient
    (j : U ⟶ Spec (.of (LaurentPolynomial R)))
    (j' : V ⟶ Spec (.of (LaurentPolynomial S))) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map (laurentCoefficientMap f)) :
    Functor.whiskerRight (boundedAboveFlatAffineSupportedSectionLaurentUnitIso j).hom
        (boundedAboveFlatAffineSupportedSectionsMap j j' (laurentCoefficientMap f) l h) =
      Functor.whiskerLeft
        (boundedAboveFlatAffineSupportedSectionsMap j j' (laurentCoefficientMap f) l h)
        (boundedAboveFlatAffineSupportedSectionLaurentUnitIso j').hom := by
  simpa only [boundedAboveFlatAffineSupportedSectionLaurentUnitIso,
    laurentCoordinate_coefficient] using
    boundedAboveFlatAffineSupportedSectionUnitIso_coefficient_hom
      j j' (laurentCoefficientMap f) l h (laurentCoordinate R)

/-- The unchanged Laurent coordinate acts on the actual specified supported restriction map. -/
def boundedAboveFlatAffineSupportedSectionLaurentUnitHomotopy
    (j : U ⟶ Spec R) (jL : V ⟶ Spec (.of (LaurentPolynomial R)))
    [IsOpenImmersion j] [IsOpenImmersion jL] (l : V ⟶ U)
    (h : l ≫ j = jL ≫ Spec.map (laurentCoefficientInclusion R)) :
    LoopPrespectrum.Homotopy
      (boundedAboveFlatAffineSupportedSectionPrespectrumMap
        j jL (laurentCoefficientInclusion R) l h)
      (boundedAboveFlatAffineSupportedSectionPrespectrumMap
        j jL (laurentCoefficientInclusion R) l h) :=
  boundedAboveFlatAffineSupportedSectionUnitHomotopy
    j jL (laurentCoefficientInclusion R) l h (laurentCoordinate R)

end AlgebraicGeometry.Scheme.Modules

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SupportedSectionLaurentUnit.lean:38-81"
  "adaptation" "Actual supported forward and inverse Laurent unit with coefficient naturality"]
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSupportedSectionLaurentUnitIso
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSupportedSectionLaurentUnitIso_hom_original
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSupportedSectionLaurentUnitIso_inv_original
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSupportedSectionLaurentUnitIso_coefficient
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSupportedSectionLaurentUnitHomotopy
