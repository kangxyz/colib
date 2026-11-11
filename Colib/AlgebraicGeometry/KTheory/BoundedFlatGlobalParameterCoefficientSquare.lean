/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterCoefficientTrack
public import Colib.KTheory.Bass.StrictDiagramIndexChange
public import Colib.Topology.Prespectrum.StrictSquareSeedNaturality
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeNaturalSeed

/-! # The actual original integral Spec-to-fine comparison -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient
open GlobalSupportedSection
open GlobalSectionChangeIndex

/-- The original parameter ambient prespectrum diagram. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalParameterCoefficientSquare.lean:31"
  "adaptation" "Actual Spec row, whole original scalar/null seed, finite and telescope maps"]
def parameterDiagram (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) :
    Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{u+1} := ParameterModels.ambient Q.left ⋙ prespectrumFunctor

/-- The exact Model row isomorphism realized without replacing its component maps. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalParameterCoefficientSquare.lean:35"
  "adaptation" "Actual Spec row, whole original scalar/null seed, finite and telescope maps"]
def rowComparison (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) :
    specUnder ⋙ parameterDiagram Q ⟶ globalRow Q ⋙ prespectrumFunctor :=
  Functor.whiskerRight (parameterRowModelIso Q).hom prespectrumFunctor

/-- All four affine index isomorphisms followed by the actual Model row comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalParameterCoefficientSquare.lean:40"
  "adaptation" "Actual Spec row, whole original scalar/null seed, finite and telescope maps"]
def squareComparison (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (parameterDiagram Q).mapArrow.mapArrow.obj (square (specUnder.obj a)) ⟶
      (globalRow Q ⋙ prespectrumFunctor).mapArrow.mapArrow.obj (laurentUnderSquare _ a) :=
  (parameterDiagram Q).mapArrow.mapArrow.map (specSquareIso a).hom ≫
    diagramSquareMap (rowComparison Q) (laurentUnderSquare _ a)

/-- The source component is exactly the actual ambient row comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalParameterCoefficientSquare.lean:48"
  "adaptation" "Actual Spec row, whole original scalar/null seed, finite and telescope maps"]
theorem squareComparison_source (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (squareComparison Q a).left.left = (rowComparison Q).app a := by
  change (parameterDiagram Q).map (𝟙 _) ≫ (rowComparison Q).app a = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- The Laurent component retains the complete original product comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalParameterCoefficientSquare.lean:55"
  "adaptation" "Actual Spec row, whole original scalar/null seed, finite and telescope maps"]
theorem squareComparison_laurent (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (squareComparison Q a).right.right =
      prespectrumMap (boundedAboveFlatGlobalSectionModelFunctor.map (laurentParameterIso Q
        a).hom.op) := by
  change (parameterDiagram Q).map (laurentSpecIso a.right).hom.op ≫
    prespectrumMap ((parameterRowModelIso Q).hom.app ((laurentUnderFunctor _).obj a)) = _
  rw [parameterRowModelIso_hom_app]
  change prespectrumFunctor.map (boundedAboveFlatGlobalSectionModelFunctor.map
      ((baseProductFunctor (specULiftZIsTerminal.from Q.left)).map (laurentSpecIso
        a.right).hom).op) ≫
    prespectrumFunctor.map (boundedAboveFlatGlobalSectionModelFunctor.map
      (canonicalRowIso Q ((laurentUnderFunctor _).obj a)).hom.op) = _
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp]
  rfl

end AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient

