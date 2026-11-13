/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSupportedParameterCoefficientTrack
public import Colib.KTheory.Bass.StrictDiagramIndexChange
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeCoefficientSeedNaturality

/-!
# The original supported seed under the actual integral Spec row

The actual affine index square followed by the supported Model row isomorphism preserves
every original unit-track time. The full null/unit/null seed square follows using the
original strict-square source null, with no new compatibility hypothesis.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedParameterCoefficient
open GlobalSectionChangeIndex GlobalSupportedSection ParameterLaurentTrack
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

/-- The original supported prespectrum diagram for every scheme parameter. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSupportedParameterCoefficientSeed.lean:36"
  "adaptation" "Original supported Spec unit, every track time and actual seed square"]
def parameterDiagram : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{u+1} :=
  ParameterModels.supported f.left ⋙ prespectrumFunctor

/-- The actual supported Model row isomorphism, realized on original prespectra. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSupportedParameterCoefficientSeed.lean:40"
  "adaptation" "Original supported Spec unit, every track time and actual seed square"]
def rowComparison : specUnder ⋙ parameterDiagram f ⟶ supportedRow f ⋙ prespectrumFunctor :=
  Functor.whiskerRight (parameterSupportedRowIso f).hom prespectrumFunctor

/-- The four actual affine index corners followed by the supported row comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSupportedParameterCoefficientSeed.lean:44"
  "adaptation" "Original supported Spec unit, every track time and actual seed square"]
def squareComparison (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (parameterDiagram f).mapArrow.mapArrow.obj (square (specUnder.obj a)) ⟶
      (supportedRow f ⋙ prespectrumFunctor).mapArrow.mapArrow.obj (laurentUnderSquare _ a) :=
  (parameterDiagram f).mapArrow.mapArrow.map (specSquareIso a).hom ≫
    diagramSquareMap (rowComparison f) (laurentUnderSquare _ a)

/-- The source corner is the unchanged supported row comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSupportedParameterCoefficientSeed.lean:51"
  "adaptation" "Original supported Spec unit, every track time and actual seed square"]
theorem squareComparison_source (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (squareComparison f a).left.left = (rowComparison f).app a := by
  change (parameterDiagram f).map (𝟙 _) ≫ (rowComparison f).app a = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- The Laurent corner is the complete original supported Laurent Model map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSupportedParameterCoefficientSeed.lean:57"
  "adaptation" "Original supported Spec unit, every track time and actual seed square"]
theorem squareComparison_laurent (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (squareComparison f a).right.right = prespectrumMap (laurentModelMap f a) := by
  change prespectrumFunctor.map
      ((ParameterModels.supported f.left).map (laurentSpecIso a.right).hom.op) ≫
    prespectrumFunctor.map ((parameterSupportedRowIso f).hom.app
      ((laurentUnderFunctor _).obj a)) = _
  exact (prespectrumFunctor.map_comp _ _).symm

/-- The actual index-change isomorphism followed by Bass functoriality of the original row. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSupportedParameterCoefficientSeed.lean:66"
  "adaptation" "Original supported Spec unit, every track time and actual seed square"]
def bassComparison :
    specUnder ⋙ (strictDiagramFunctor squareFunctor).obj (parameterDiagram f) ⟶
      (strictDiagramFunctor (laurentUnderSquareFunctor _)).obj
        (supportedRow f ⋙ prespectrumFunctor) :=
  (StrictDiagramIndexChange.iso specUnder (laurentUnderSquareFunctor _)
      squareFunctor specSquare (parameterDiagram f)).hom ≫
    (strictDiagramFunctor (laurentUnderSquareFunctor _)).map (rowComparison f)

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

/-- At every coefficient, the Bass comparison is the original full square cone-loop map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSupportedParameterCoefficientSeed.lean:88"
  "adaptation" "Original supported Spec unit, every track time and actual seed square"]
theorem bassComparison_app (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (bassComparison f).app a = strictSquareLoopedConeFunctor.map (squareComparison f a) := by
  exact comparison_component (parameterDiagram f) (supportedRow f ⋙ prespectrumFunctor)
    (rowComparison f) a

/-- The complete affine square preserves all original supported scalar-track values. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSupportedParameterCoefficientSeed.lean:94"
  "adaptation" "Original supported Spec unit, every track time and actual seed square"]
theorem squareComparison_track (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (n : ℕ) (r : unitInterval)
    (x : (parameterDiagram f).obj (specUnder.obj a) |>.space n) :
    (squareComparison f a).right.right.map n
        (((supportedTrack f.left).homotopy (specUnder.obj a)).level n (r,x)) =
      ((supportedLaurentAction f).track.homotopy a).level n
        (r, (squareComparison f a).left.left.map n x) := by
  rw [squareComparison_source, squareComparison_laurent]
  exact track_square f a n r x

/-- The original supported null/unit/null seed commutes with the actual integral Spec row. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSupportedParameterCoefficientSeed.lean:105"
  "adaptation" "Original supported Spec unit, every track time and actual seed square"]
theorem seed_square :
    Functor.whiskerLeft specUnder (SchemeNaturalSeed.seed (supportedTrack f.left)) ≫
        bassComparison f =
      rowComparison f ≫ (supportedLaurentAction f).track.seed := by
  apply NatTrans.ext
  funext a
  rw [NatTrans.comp_app, NatTrans.comp_app, bassComparison_app]
  change (SchemeNaturalSeed.seed (supportedTrack f.left)).app (specUnder.obj a) ≫
    strictSquareLoopedConeFunctor.map (squareComparison f a) = _
  rw [SchemeCoefficientSeedNaturality.seed_naturality
    (supportedTrack f.left) (supportedLaurentAction f).track (specUnder.obj a) a
    (squareComparison f a) (squareComparison_track f a)]
  rw [squareComparison_source]

end AlgebraicGeometry.Scheme.Modules.GlobalSupportedParameterCoefficient

