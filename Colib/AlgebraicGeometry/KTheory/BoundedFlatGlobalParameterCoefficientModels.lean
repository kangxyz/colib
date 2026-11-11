/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatGlobalSupportedPairDiagram
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalCoefficientRow
public import Colib.AlgebraicGeometry.Scheme.IntegerBaseCanonicalRow

/-! # The actual original integral Spec-to-fine comparison -/
@[expose] public section
noncomputable section
open CategoryTheory Topology AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CategoryTheory.Waldhausen.IteratedS
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
open GlobalSupportedSection

/-- The actual symmetry and terminal-map transport give an isomorphism of original Model rows. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalParameterCoefficientModels.lean:25"
  "adaptation" "Actual Spec row, whole original scalar/null seed, finite and telescope maps"]
def parameterRowModelIso (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) :
    specUnder ⋙ ParameterModels.ambient Q.left ≅ globalRow Q :=
  (Functor.associator specUnder (baseProductFunctor (specULiftZIsTerminal.from Q.left)).op
    boundedAboveFlatGlobalSectionModelFunctor).symm ≪≫
    Functor.isoWhiskerRight (canonicalParameterRowIso Q) boundedAboveFlatGlobalSectionModelFunctor
      ≪≫
      Functor.associator (row Q) (functor (CommRingCat.of (ULift.{u} ℤ)))
        boundedAboveFlatGlobalSectionModelFunctor

/-- Its component is exactly the original global pullback along the complete geometric iso. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalParameterCoefficientModels.lean:32"
  "adaptation" "Actual Spec row, whole original scalar/null seed, finite and telescope maps"]
theorem parameterRowModelIso_hom_app (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (parameterRowModelIso Q).hom.app a = boundedAboveFlatGlobalSectionModelFunctor.map
      (canonicalRowIso Q a).hom.op := by
  change 𝟙 _ ≫ boundedAboveFlatGlobalSectionModelFunctor.map (canonicalRowIso Q a).hom.op ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

/-- Compose actual row symmetry with the unchanged original coefficient restriction. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalParameterCoefficientModels.lean:39"
  "adaptation" "Actual Spec row, whole original scalar/null seed, finite and telescope maps"]
def parameterCoefficientRestriction (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) :
    specUnder ⋙ ParameterModels.ambient Q.left ⟶ boundedAboveFlatCoefficientSectionModelRow Q :=
  (parameterRowModelIso Q).hom ≫ rowRestriction Q

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex

