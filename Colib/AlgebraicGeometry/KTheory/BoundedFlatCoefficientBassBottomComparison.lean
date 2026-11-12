/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryOpenRestrictionStages
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryGradedBassVanishing
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedGradedBassTower

public import Colib.RingTheory.Polynomial.LaurentUnderSquare
public import Colib.KTheory.Bass.ModelDiagramBottomNaturality
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientTwoChartStableSequence
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedFiberBassTower

/-!
Source:
`Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientBassBottomComparison.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Actual finite native coefficient-family bottom contractions

These comparisons use the existing native finite Bass diagrams and their original
coefficient maps. They identify the original two-chart cokernel with the actual next
finite-stage bottom. They do not redefine the original scheme/supported negative groups,
and do not assert stabilization of any original seed.
-/

@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
open Topology
open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum
open KTheory.Bass
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}}

/-- The original fine ambient coefficient family has its genuine natural bottom contraction. -/
def boundedAboveFlatCoefficientAmbientBassBottomContractionIso (Q : Over (Spec R)) (i : ℕ) :
    KTheory.Bass.TwoChart.contraction (underToLaurent R) (underToLaurentInvert R)
      (boundedAboveFlatCoefficientAmbientBassDiagram Q i ⋙ stableHomotopyFunctor (-(i : ℤ))) ≅
    boundedAboveFlatCoefficientAmbientBassDiagram Q (i + 1) ⋙
      stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ)) :=
  modelDiagramBottomContractionIso (boundedAboveFlatCoefficientSectionModelRow Q) i

/-- Original ambient Laurent representatives use the unchanged cone inclusion and signed shift.
-/
@[reassoc]
theorem boundedAboveFlatCoefficientAmbientBassBottomContractionIso_π
    (Q : Over (Spec R)) (i : ℕ) (a : Under R) :
    (KTheory.Bass.TwoChart.contractionπ (underToLaurent R) (underToLaurentInvert R)
      (boundedAboveFlatCoefficientAmbientBassDiagram Q i ⋙
        stableHomotopyFunctor (-(i : ℤ)))).app a ≫
      (boundedAboveFlatCoefficientAmbientBassBottomContractionIso Q i).hom.app a =
    (stableHomotopyFunctor (-(i : ℤ))).map (mappingConeInclusion (StrictSquare.comparison
      ((boundedAboveFlatCoefficientAmbientBassDiagram Q i).mapArrow.mapArrow.obj
        (laurentUnderSquare R a)))) ≫
      (modelDiagramBottomSuccessorIso (boundedAboveFlatCoefficientSectionModelRow Q) i).inv.app a :=
  modelDiagramBottomContractionIso_π (boundedAboveFlatCoefficientSectionModelRow Q) i a

variable {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left]

/-- The original fine supported family has the actual two-chart bottom comparison. -/
def boundedAboveFlatCoefficientSupportedBassBottomContractionIso (i : ℕ) :
    KTheory.Bass.TwoChart.contraction (underToLaurent R) (underToLaurentInvert R)
      (boundedAboveFlatCoefficientSupportedBassDiagram f i ⋙ stableHomotopyFunctor (-(i : ℤ))) ≅
    boundedAboveFlatCoefficientSupportedBassDiagram f (i + 1) ⋙
      stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ)) :=
  modelDiagramBottomContractionIso (boundedAboveFlatCoefficientSupportedModelFunctor f) i

/-- The original coarse relative-open family has the same genuine natural comparison. -/
def boundedAboveFlatCoefficientOpenBassBottomContractionIso (i : ℕ) :
    KTheory.Bass.TwoChart.contraction (underToLaurent R) (underToLaurentInvert R)
      (boundedAboveFlatCoefficientOpenBassDiagram f i ⋙ stableHomotopyFunctor (-(i : ℤ))) ≅
    boundedAboveFlatCoefficientOpenBassDiagram f (i + 1) ⋙
      stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ)) :=
  modelDiagramBottomContractionIso (boundedAboveFlatCoefficientOpenModelFunctor f) i

/-- The unchanged fine open family has its actual next-stage bottom contraction. -/
def boundedAboveFlatCoefficientFullOpenBassBottomContractionIso (i : ℕ) :
    KTheory.Bass.TwoChart.contraction (underToLaurent R) (underToLaurentInvert R)
      (boundedAboveFlatCoefficientFullOpenBassDiagram f i ⋙ stableHomotopyFunctor (-(i : ℤ))) ≅
    boundedAboveFlatCoefficientFullOpenBassDiagram f (i + 1) ⋙
      stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ)) :=
  modelDiagramBottomContractionIso (boundedAboveFlatCoefficientFullOpenModelFunctor f) i

/-- Supported Laurent representatives keep their actual original cone inclusion and signed shift.
-/
@[reassoc]
theorem boundedAboveFlatCoefficientSupportedBassBottomContractionIso_π (i : ℕ) (a : Under R) :
    (KTheory.Bass.TwoChart.contractionπ (underToLaurent R) (underToLaurentInvert R)
      (boundedAboveFlatCoefficientSupportedBassDiagram f i ⋙
        stableHomotopyFunctor (-(i : ℤ)))).app a ≫
      (boundedAboveFlatCoefficientSupportedBassBottomContractionIso f i).hom.app a =
    (stableHomotopyFunctor (-(i : ℤ))).map (mappingConeInclusion (StrictSquare.comparison
      ((boundedAboveFlatCoefficientSupportedBassDiagram f i).mapArrow.mapArrow.obj
        (laurentUnderSquare R a)))) ≫
      (modelDiagramBottomSuccessorIso
    (boundedAboveFlatCoefficientSupportedModelFunctor f) i).inv.app
        a :=
  modelDiagramBottomContractionIso_π (boundedAboveFlatCoefficientSupportedModelFunctor f) i a

/-- The bottom comparison preserves the existing finite supported-to-ambient map at its successor.
-/
@[reassoc]
theorem boundedAboveFlatCoefficientSupportedBassBottomContractionIso_forget
    (i : ℕ) (a : Under R) :
    (KTheory.Bass.TwoChart.contractionMap (underToLaurent R) (underToLaurentInvert R)
      (Functor.whiskerRight (boundedAboveFlatCoefficientSupportedBassForget f i)
        (stableHomotopyFunctor (-(i : ℤ))))).app a ≫
      (boundedAboveFlatCoefficientAmbientBassBottomContractionIso Q i).hom.app a =
    (boundedAboveFlatCoefficientSupportedBassBottomContractionIso f i).hom.app a ≫
      (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
        ((boundedAboveFlatCoefficientSupportedBassForget f (i + 1)).app a) :=
  modelDiagramBottomContractionIso_map
    (boundedAboveFlatCoefficientSupportedForgetPrespectrumTransformation f) i a

/-- The actual fine-to-coarse native open map survives the same bottom comparison. -/
@[reassoc]
theorem boundedAboveFlatCoefficientAmbientBassBottomContractionIso_open
    (i : ℕ) (a : Under R) :
    (KTheory.Bass.TwoChart.contractionMap (underToLaurent R) (underToLaurentInvert R)
      (Functor.whiskerRight (boundedAboveFlatCoefficientAmbientBassOpen f i)
        (stableHomotopyFunctor (-(i : ℤ))))).app a ≫
      (boundedAboveFlatCoefficientOpenBassBottomContractionIso f i).hom.app a =
    (boundedAboveFlatCoefficientAmbientBassBottomContractionIso Q i).hom.app a ≫
      (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
        ((boundedAboveFlatCoefficientAmbientBassOpen f (i + 1)).app a) :=
  modelDiagramBottomContractionIso_map
    (boundedAboveFlatCoefficientAmbientOpenPrespectrumTransformation f) i a

/-- The existing native coarse-to-fine open restriction is retained at the actual successor. -/
@[reassoc]
theorem boundedAboveFlatCoefficientOpenBassBottomContractionIso_restriction
    (i : ℕ) (a : Under R) :
    (KTheory.Bass.TwoChart.contractionMap (underToLaurent R) (underToLaurentInvert R)
      (Functor.whiskerRight (boundedAboveFlatCoefficientOpenBassRestriction f i)
        (stableHomotopyFunctor (-(i : ℤ))))).app a ≫
      (boundedAboveFlatCoefficientFullOpenBassBottomContractionIso f i).hom.app a =
    (boundedAboveFlatCoefficientOpenBassBottomContractionIso f i).hom.app a ≫
      (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
        ((boundedAboveFlatCoefficientOpenBassRestriction f (i + 1)).app a) :=
  modelDiagramBottomContractionIso_map
    (boundedAboveFlatCoefficientOpenRestrictionPrespectrumTransformation f) i a

variable (T : Q.left.Opens)

/-- The actual auxiliary-supported ambient family has the original chart bottom cokernel. -/
def boundedAboveFlatCoefficientSupportedAmbientBassBottomContractionIso (i : ℕ) :
    KTheory.Bass.TwoChart.contraction (underToLaurent R) (underToLaurentInvert R)
      (boundedAboveFlatCoefficientSupportedAmbientBassDiagram T i ⋙
        stableHomotopyFunctor (-(i : ℤ))) ≅
    boundedAboveFlatCoefficientSupportedAmbientBassDiagram T (i + 1) ⋙
      stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ)) :=
  modelDiagramBottomContractionIso (boundedAboveFlatCoefficientSupportedAmbientModelFunctor T) i

/-- The original intersection-support fiber has its actual next-stage bottom contraction. -/
def boundedAboveFlatCoefficientSupportedFiberBassBottomContractionIso (i : ℕ) :
    KTheory.Bass.TwoChart.contraction (underToLaurent R) (underToLaurentInvert R)
      (boundedAboveFlatCoefficientSupportedFiberBassDiagram f T i ⋙
        stableHomotopyFunctor (-(i : ℤ))) ≅
    boundedAboveFlatCoefficientSupportedFiberBassDiagram f T (i + 1) ⋙
      stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ)) :=
  modelDiagramBottomContractionIso (boundedAboveFlatCoefficientSupportedFiberModelFunctor f T) i

/-- The actual auxiliary-supported coarse open stages retain their original chart bottom groups.
-/
def boundedAboveFlatCoefficientSupportedOpenBassBottomContractionIso (i : ℕ) :
    KTheory.Bass.TwoChart.contraction (underToLaurent R) (underToLaurentInvert R)
      (boundedAboveFlatCoefficientSupportedOpenBassDiagram f T i ⋙
        stableHomotopyFunctor (-(i : ℤ))) ≅
    boundedAboveFlatCoefficientSupportedOpenBassDiagram f T (i + 1) ⋙
      stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ)) :=
  modelDiagramBottomContractionIso (boundedAboveFlatCoefficientSupportedOpenModelFunctor f T) i

/-- The original auxiliary-supported fine open family has its genuine bottom contraction. -/
def boundedAboveFlatCoefficientSupportedFullOpenBassBottomContractionIso (i : ℕ) :
    KTheory.Bass.TwoChart.contraction (underToLaurent R) (underToLaurentInvert R)
      (boundedAboveFlatCoefficientSupportedFullOpenBassDiagram f T i ⋙
        stableHomotopyFunctor (-(i : ℤ))) ≅
    boundedAboveFlatCoefficientSupportedFullOpenBassDiagram f T (i + 1) ⋙
      stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ)) :=
  modelDiagramBottomContractionIso (boundedAboveFlatCoefficientSupportedFullOpenModelFunctor f T) i

/-- The original intersection-support forget map is retained at the successor bottom. -/
@[reassoc]
theorem boundedAboveFlatCoefficientSupportedFiberBassBottomContractionIso_forget
    (i : ℕ) (a : Under R) :
    (KTheory.Bass.TwoChart.contractionMap (underToLaurent R) (underToLaurentInvert R)
      (Functor.whiskerRight (boundedAboveFlatCoefficientSupportedFiberBassForget f T i)
        (stableHomotopyFunctor (-(i : ℤ))))).app a ≫
      (boundedAboveFlatCoefficientSupportedAmbientBassBottomContractionIso T i).hom.app a =
    (boundedAboveFlatCoefficientSupportedFiberBassBottomContractionIso f T i).hom.app a ≫
      (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
        ((boundedAboveFlatCoefficientSupportedFiberBassForget f T (i + 1)).app a) :=
  modelDiagramBottomContractionIso_map
    (boundedAboveFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T) i a

omit [IsOpenImmersion f.left] in
/-- The same original auxiliary-supported r-map is preserved by the bottom comparison. -/
@[reassoc]
theorem boundedAboveFlatCoefficientSupportedOpenBassBottomContractionIso_restriction
    (i : ℕ) (a : Under R) :
    (KTheory.Bass.TwoChart.contractionMap (underToLaurent R) (underToLaurentInvert R)
      (Functor.whiskerRight (boundedAboveFlatCoefficientSupportedOpenBassRestriction f T i)
        (stableHomotopyFunctor (-(i : ℤ))))).app a ≫
      (boundedAboveFlatCoefficientSupportedFullOpenBassBottomContractionIso f T i).hom.app a =
    (boundedAboveFlatCoefficientSupportedOpenBassBottomContractionIso f T i).hom.app a ≫
      (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
        ((boundedAboveFlatCoefficientSupportedOpenBassRestriction f T (i + 1)).app a) :=
  modelDiagramBottomContractionIso_map
    (boundedAboveFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T) i a

variable [CompactSpace P.left] [CompactSpace Q.left]

/-- The original graded native Model stages have the same actual chart bottom contraction. -/
def boundedAboveFlatCoefficientGradedOpenBassBottomContractionIso (i : ℕ) :
    KTheory.Bass.TwoChart.contraction (underToLaurent R) (underToLaurentInvert R)
      (boundedAboveFlatCoefficientGradedOpenBassDiagram f i ⋙ stableHomotopyFunctor (-(i : ℤ))) ≅
    boundedAboveFlatCoefficientGradedOpenBassDiagram f (i + 1) ⋙
      stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ)) :=
  modelDiagramBottomContractionIso (boundedAboveFlatCoefficientGradedOpenModelFunctor f) i

/-- The auxiliary-supported graded native Model stages retain their actual bottom contraction. -/
def boundedAboveFlatCoefficientSupportedGradedOpenBassBottomContractionIso (i : ℕ) :
    KTheory.Bass.TwoChart.contraction (underToLaurent R) (underToLaurentInvert R)
      (boundedAboveFlatCoefficientSupportedGradedOpenBassDiagram f T i ⋙
        stableHomotopyFunctor (-(i : ℤ))) ≅
    boundedAboveFlatCoefficientSupportedGradedOpenBassDiagram f T (i + 1) ⋙
      stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ)) :=
  modelDiagramBottomContractionIso
    (boundedAboveFlatCoefficientSupportedGradedOpenModelFunctor f T) i

end AlgebraicGeometry.Scheme.Modules
