/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterCoefficientSquare

/-! # The actual original integral Spec-to-fine comparison -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient
open GlobalSupportedSection
open GlobalSectionChangeIndex

/-- The complete Bass comparison uses the affine index square and the actual global Model row. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalParameterCoefficientSeed.lean:26"
  "adaptation" "Actual Spec row, whole original scalar/null seed, finite and telescope maps"]
def bassComparison (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) :
    specUnder ⋙ (strictDiagramFunctor squareFunctor).obj (parameterDiagram Q) ⟶
      (strictDiagramFunctor (laurentUnderSquareFunctor _)).obj
        (globalRow Q ⋙ prespectrumFunctor) :=
  (StrictDiagramIndexChange.iso specUnder _ squareFunctor specSquare (parameterDiagram Q)).hom ≫
    (strictDiagramFunctor (laurentUnderSquareFunctor _)).map (rowComparison Q)

private theorem comparison_component
    (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{u + 1})
    (G : Under (CommRingCat.of (ULift.{u} ℤ)) ⥤ LoopPrespectrum.{u + 1})
    (η : specUnder ⋙ F ⟶ G) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    ((StrictDiagramIndexChange.iso specUnder _ squareFunctor specSquare F).hom ≫
        (strictDiagramFunctor (laurentUnderSquareFunctor _)).map η).app a =
      strictSquareLoopedConeFunctor.map
        (F.mapArrow.mapArrow.map (specSquareIso a).hom ≫
          diagramSquareMap η (laurentUnderSquare _ a)) := by
  exact (strictSquareLoopedConeFunctor.map_comp
    (F.mapArrow.mapArrow.map (specSquareIso a).hom)
    (diagramSquareMap η (laurentUnderSquare _ a))).symm

/-- Every component is the original looped-cone map of the complete four-corner comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalParameterCoefficientSeed.lean:47"
  "adaptation" "Actual Spec row, whole original scalar/null seed, finite and telescope maps"]
theorem bassComparison_app (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (bassComparison Q).app a = strictSquareLoopedConeFunctor.map (squareComparison Q a) := by
  exact comparison_component (parameterDiagram Q) (globalRow Q ⋙ prespectrumFunctor)
    (rowComparison Q) a

/-- The complete four-corner map preserves every time of the actual original scalar tracks. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalParameterCoefficientSeed.lean:54"
  "adaptation" "Actual Spec row, whole original scalar/null seed, finite and telescope maps"]
theorem squareComparison_track
    (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ) (r : unitInterval)
    (x : ((parameterDiagram Q).obj (specUnder.obj a)).space n) :
    (squareComparison Q a).right.right.map n
        (((ParameterLaurentTrack.ambientTrack Q.left).homotopy (specUnder.obj a)).level n (r, x)) =
      (((globalLaurentAction Q).track.homotopy a).level n
        (r, (squareComparison Q a).left.left.map n x)) := by
  rw [squareComparison_laurent, squareComparison_source]
  change _ = (((globalLaurentAction Q).track.homotopy a).level n
    (r, (prespectrumMap ((parameterRowModelIso Q).hom.app a)).map n x))
  rw [parameterRowModelIso_hom_app]
  exact track_square Q a n r x

end AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient

