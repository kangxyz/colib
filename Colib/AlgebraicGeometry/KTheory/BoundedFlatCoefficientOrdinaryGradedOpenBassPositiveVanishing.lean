/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryGradedBassVanishing
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryOpenConeStable
public import Colib.KTheory.Bass.ModelDiagramTwoChartStableSequence
public import Colib.KTheory.Bass.TwoChartStableVanishing
public import Mathlib.Algebra.Category.Grp.Zero

/-!
# Positive-degree vanishing at the original first graded Bass stage

The original image-quotient graded Model vanishes away from degree zero. Its realized spectral
Bass row therefore makes its original first Bass stage vanish in positive degrees. No assertion
about degree zero or concentration in degree minus one is used or made.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
  CoefficientGradedOpenBassPositiveVanishing.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS KTheory.Bass KTheory.Bass.TwoChartStable
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open CommRingCat.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]

attribute [local irreducible] prespectrum

private theorem firstBass_subsingleton (F : Under R ⥤ WideSubcategory preservesZero.{u + 1})
    (a : Under R) (d : ℤ)
    (hplus : Subsingleton (stableHomotopyGroup
      (prespectrum (F.obj ((polynomialUnderFunctor R).obj a))) d))
    (hlaurent : Subsingleton (stableHomotopyGroup
      (prespectrum (F.obj ((laurentUnderFunctor R).obj a))) (d + 1))) :
    Subsingleton (stableHomotopyGroup
      (((strictDiagramIterate (laurentUnderSquareFunctor R) 1).obj
        (F ⋙ prespectrumFunctor)).obj a) d) := by
  have hp : IsZero ((stableHomotopyFunctor d).obj
      (prespectrum (F.obj ((polynomialUnderFunctor R).obj a)))) := by
    let : Subsingleton ((stableHomotopyFunctor d).obj
        (prespectrum (F.obj ((polynomialUnderFunctor R).obj a)))) := hplus
    exact AddCommGrpCat.isZero_of_subsingleton _
  have hl : IsZero ((stableHomotopyFunctor (d + 1)).obj
      (prespectrum (F.obj ((laurentUnderFunctor R).obj a)))) := by
    let : Subsingleton ((stableHomotopyFunctor (d + 1)).obj
        (prespectrum (F.obj ((laurentUnderFunctor R).obj a)))) := hlaurent
    exact AddCommGrpCat.isZero_of_subsingleton _
  exact AddCommGrpCat.subsingleton_of_isZero
    (bassGroup_isZero_of_corners (modelDiagramTwoChartSquare F 0 a)
      (modelDiagramTwoChartSpectralConditions F 0 a) d hp hp hl)

/-- The actual first graded Bass stage has no positive-degree stable classes. -/
theorem boundedAboveFlatCoefficientGradedOpenBass_one_positive_subsingleton
    (a : Under R) (d : ℤ) (hd : 0 < d) :
    Subsingleton (stableHomotopyGroup
      ((boundedAboveFlatCoefficientGradedOpenBassDiagram f 1).obj a) d) :=
  firstBass_subsingleton (boundedAboveFlatCoefficientGradedOpenModelFunctor f) a d
    (boundedAboveFlatCoefficientGradedOpen_stable_subsingleton f _ d (ne_of_gt hd))
    (boundedAboveFlatCoefficientGradedOpen_stable_subsingleton f _ (d + 1) (by omega))

end AlgebraicGeometry.Scheme.Modules
