/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Polynomial.LaurentUnderSquare
public import Colib.KTheory.Bass.ModelDiagramTwoChartStableSequence
public import Colib.AlgebraicGeometry.Scheme.CoefficientLaurentProjection
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedBassTower
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedOpenBassStages

/-!
Source:
`Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientTwoChartStableSequence.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# The realized spectral Bass row for the original native coefficient families

Actual polynomial evaluation at zero gives a strict retraction on every original finite
coefficient Model stage. Finite Model geometry discharges the original plus, right-inclusion,
and span-to-Laurent cone excisions and the unchanged right-cone collapse. The resulting
all-integer row applies to the actual ambient, open, supported, and auxiliary-supported rows.
The geometric zero map below keeps the native chosen fibers and their original projections.

No chart middle exactness, classical fundamental row, seed preservation, or finite transition
equivalence is asserted here. Each family retains the hypotheses of its original Model constructor.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.BaseChange.Coefficients


open CommRingCat.PolynomialLaurent

noncomputable section
open Topology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open KTheory.Bass
  AlgebraicGeometry.Scheme.BaseChange.Coefficients
open KTheory.Bass.TwoChartStable
universe u
namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}}

/-- The actual zero section between the original chosen native coefficient fibers. -/
def boundedAboveFlatCoefficientPolynomialZero (Q : Over (Spec R)) (a : Under R) :
    space (op Q, a) ⟶ space (op Q, (polynomialUnderFunctor R).obj a) :=
  coefficientMap Q (modelDiagramPolynomialZero a)

/-- The native zero section lies over the original affine polynomial evaluation at zero. -/
@[reassoc]
theorem boundedAboveFlatCoefficientPolynomialZero_coefficientProjection
    (Q : Over (Spec R)) (a : Under R) :
    boundedAboveFlatCoefficientPolynomialZero Q a ≫
      coefficientProjection (op Q, (polynomialUnderFunctor R).obj a) =
        coefficientProjection (op Q, a) ≫
          Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : a.right))) :=
  coefficientMap_coefficientProjection Q (modelDiagramPolynomialZero a)

/-- The original native polynomial projection is strictly split by this actual zero section. -/
@[reassoc]
theorem boundedAboveFlatCoefficientPolynomialZero_projection (Q : Over (Spec R)) (a : Under R) :
    boundedAboveFlatCoefficientPolynomialZero Q a ≫
      coefficientMap Q ((polynomialUnderCoefficient R).app a) =
      𝟙 (space (op Q, a)) := by
  unfold boundedAboveFlatCoefficientPolynomialZero
  rw [← coefficientMap_comp, modelDiagramPolynomialCoefficient_zero]
  change AlgebraicGeometry.Scheme.BaseChange.Coefficients.map (𝟙 (op Q, a)) = _
  exact AlgebraicGeometry.Scheme.BaseChange.Coefficients.map_id (op Q, a)

/-- All structural-row inputs are constructed on every original fine ambient coefficient stage.
-/
def boundedAboveFlatCoefficientAmbientTwoChartSpectralConditions
    (Q : Over (Spec R)) (i : ℕ) (a : Under R) :
    SpectralConditions ((boundedAboveFlatCoefficientAmbientBassDiagram Q i).mapArrow.mapArrow.obj
      (laurentUnderSquare R a)) :=
  modelDiagramTwoChartSpectralConditions (boundedAboveFlatCoefficientSectionModelRow Q) i a

/-- The actual ambient spectral Bass row, retaining its original cone inclusion and shift. -/
def boundedAboveFlatCoefficientAmbientTwoChartSequence
    (Q : Over (Spec R)) (i : ℕ) (a : Under R) (d : ℤ) : ShortComplex AddCommGrpCat :=
  bassSequence ((boundedAboveFlatCoefficientAmbientBassDiagram Q i).mapArrow.mapArrow.obj
    (laurentUnderSquare R a)) (boundedAboveFlatCoefficientAmbientTwoChartSpectralConditions Q i a) d

/-- The native fine ambient spectral row is short exact in every signed degree. -/
theorem boundedAboveFlatCoefficientAmbientTwoChartSequence_shortExact
    (Q : Over (Spec R)) (i : ℕ) (a : Under R) (d : ℤ) :
    (boundedAboveFlatCoefficientAmbientTwoChartSequence Q i a d).ShortExact :=
  bassSequence_shortExact _ _ d

variable {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left]

/-- Every actual fine supported coefficient stage has the full original spectral-row inputs. -/
def boundedAboveFlatCoefficientSupportedTwoChartSpectralConditions (i : ℕ) (a : Under R) :
    SpectralConditions ((boundedAboveFlatCoefficientSupportedBassDiagram f i).mapArrow.mapArrow.obj
      (laurentUnderSquare R a)) :=
  modelDiagramTwoChartSpectralConditions (boundedAboveFlatCoefficientSupportedModelFunctor f) i a

/-- The actual supported spectral row, using the unchanged native supported Bass diagram. -/
def boundedAboveFlatCoefficientSupportedTwoChartSequence (i : ℕ) (a : Under R) (d : ℤ) :
    ShortComplex AddCommGrpCat :=
  bassSequence ((boundedAboveFlatCoefficientSupportedBassDiagram f i).mapArrow.mapArrow.obj
    (laurentUnderSquare R a))
    (boundedAboveFlatCoefficientSupportedTwoChartSpectralConditions f i a) d

/-- The original supported spectral row is short exact in every signed degree. -/
theorem boundedAboveFlatCoefficientSupportedTwoChartSequence_shortExact
    (i : ℕ) (a : Under R) (d : ℤ) :
    (boundedAboveFlatCoefficientSupportedTwoChartSequence f i a d).ShortExact :=
  bassSequence_shortExact _ _ d

/-- Actual coarse open Models discharge every retained condition at all original finite stages.
-/
def boundedAboveFlatCoefficientOpenTwoChartSpectralConditions (i : ℕ) (a : Under R) :
    SpectralConditions ((boundedAboveFlatCoefficientOpenBassDiagram f i).mapArrow.mapArrow.obj
      (laurentUnderSquare R a)) :=
  modelDiagramTwoChartSpectralConditions (boundedAboveFlatCoefficientOpenModelFunctor f) i a

/-- The actual coarse open spectral row, with both original Laurent chart maps. -/
def boundedAboveFlatCoefficientOpenTwoChartSequence (i : ℕ) (a : Under R) (d : ℤ) :
    ShortComplex AddCommGrpCat :=
  bassSequence ((boundedAboveFlatCoefficientOpenBassDiagram f i).mapArrow.mapArrow.obj
    (laurentUnderSquare R a)) (boundedAboveFlatCoefficientOpenTwoChartSpectralConditions f i a) d

/-- The original coarse open spectral row is short exact in every signed degree. -/
theorem boundedAboveFlatCoefficientOpenTwoChartSequence_shortExact
    (i : ℕ) (a : Under R) (d : ℤ) :
    (boundedAboveFlatCoefficientOpenTwoChartSequence f i a d).ShortExact :=
  bassSequence_shortExact _ _ d

/-- The fine native open coefficient stages have the same completely realized inputs. -/
def boundedAboveFlatCoefficientFullOpenTwoChartSpectralConditions (i : ℕ) (a : Under R) :
    SpectralConditions ((boundedAboveFlatCoefficientFullOpenBassDiagram f i).mapArrow.mapArrow.obj
      (laurentUnderSquare R a)) :=
  modelDiagramTwoChartSpectralConditions (boundedAboveFlatCoefficientFullOpenModelFunctor f) i a

/-- The actual fine open spectral row of the unchanged open-side Bass diagram. -/
def boundedAboveFlatCoefficientFullOpenTwoChartSequence (i : ℕ) (a : Under R) (d : ℤ) :
    ShortComplex AddCommGrpCat :=
  bassSequence ((boundedAboveFlatCoefficientFullOpenBassDiagram f i).mapArrow.mapArrow.obj
    (laurentUnderSquare R a))
    (boundedAboveFlatCoefficientFullOpenTwoChartSpectralConditions f i a) d

omit [IsOpenImmersion f.left] in
/-- The original fine open spectral row is short exact in every signed degree. -/
theorem boundedAboveFlatCoefficientFullOpenTwoChartSequence_shortExact
    (i : ℕ) (a : Under R) (d : ℤ) :
    (boundedAboveFlatCoefficientFullOpenTwoChartSequence f i a d).ShortExact :=
  bassSequence_shortExact _ _ d

variable (T : Q.left.Opens)

/-- Actual auxiliary-supported ambient Models satisfy all inputs at every finite Bass stage. -/
def boundedAboveFlatCoefficientSupportedAmbientTwoChartSpectralConditions (i : ℕ) (a : Under R) :
    SpectralConditions (modelDiagramTwoChartSquare
      (boundedAboveFlatCoefficientSupportedAmbientModelFunctor T) i a) :=
  modelDiagramTwoChartSpectralConditions
    (boundedAboveFlatCoefficientSupportedAmbientModelFunctor T) i a

/-- All retained inputs are discharged for the original auxiliary-supported coarse open stage. -/
def boundedAboveFlatCoefficientSupportedOpenTwoChartSpectralConditions (i : ℕ) (a : Under R) :
    SpectralConditions
      ((boundedAboveFlatCoefficientSupportedOpenBassDiagram f T i).mapArrow.mapArrow.obj
      (laurentUnderSquare R a)) :=
  modelDiagramTwoChartSpectralConditions
    (boundedAboveFlatCoefficientSupportedOpenModelFunctor f T) i a

/-- The unchanged auxiliary-supported coarse open spectral row. -/
def boundedAboveFlatCoefficientSupportedOpenTwoChartSequence (i : ℕ) (a : Under R) (d : ℤ) :
    ShortComplex AddCommGrpCat :=
  bassSequence ((boundedAboveFlatCoefficientSupportedOpenBassDiagram f T i).mapArrow.mapArrow.obj
    (laurentUnderSquare R a))
      (boundedAboveFlatCoefficientSupportedOpenTwoChartSpectralConditions f T i a) d

omit [IsOpenImmersion f.left] in
/-- The original auxiliary-supported coarse row is short exact in every signed degree. -/
theorem boundedAboveFlatCoefficientSupportedOpenTwoChartSequence_shortExact
    (i : ℕ) (a : Under R) (d : ℤ) :
    (boundedAboveFlatCoefficientSupportedOpenTwoChartSequence f T i a d).ShortExact :=
  bassSequence_shortExact _ _ d

/-- The original auxiliary-supported fine open stage has completely realized spectral inputs. -/
def boundedAboveFlatCoefficientSupportedFullOpenTwoChartSpectralConditions (i : ℕ) (a : Under R) :
    SpectralConditions
      ((boundedAboveFlatCoefficientSupportedFullOpenBassDiagram f T i).mapArrow.mapArrow.obj
        (laurentUnderSquare R a)) :=
  modelDiagramTwoChartSpectralConditions
    (boundedAboveFlatCoefficientSupportedFullOpenModelFunctor f T) i a

/-- The unchanged auxiliary-supported fine open spectral row. -/
def boundedAboveFlatCoefficientSupportedFullOpenTwoChartSequence (i : ℕ) (a : Under R) (d : ℤ) :
    ShortComplex AddCommGrpCat :=
  bassSequence
    ((boundedAboveFlatCoefficientSupportedFullOpenBassDiagram f T i).mapArrow.mapArrow.obj
    (laurentUnderSquare R a))
      (boundedAboveFlatCoefficientSupportedFullOpenTwoChartSpectralConditions f T i a) d

omit [IsOpenImmersion f.left] in
/-- The original auxiliary-supported fine row is short exact in every signed degree. -/
theorem boundedAboveFlatCoefficientSupportedFullOpenTwoChartSequence_shortExact
    (i : ℕ) (a : Under R) (d : ℤ) :
    (boundedAboveFlatCoefficientSupportedFullOpenTwoChartSequence f T i a d).ShortExact :=
  bassSequence_shortExact _ _ d

/-- The actual auxiliary-supported closed-fiber Models satisfy the same finite-stage inputs. -/
def boundedAboveFlatCoefficientSupportedFiberTwoChartSpectralConditions (i : ℕ) (a : Under R) :
    SpectralConditions (modelDiagramTwoChartSquare
      (boundedAboveFlatCoefficientSupportedFiberModelFunctor f T) i a) :=
  modelDiagramTwoChartSpectralConditions
    (boundedAboveFlatCoefficientSupportedFiberModelFunctor f T) i a

end AlgebraicGeometry.Scheme.Modules
