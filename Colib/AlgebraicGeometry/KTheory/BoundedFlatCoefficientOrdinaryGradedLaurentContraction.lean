/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryGradedBassSeed
public import Colib.RingTheory.KTheory.Bass.StrictLaurentSeedContraction

/-! # Original ordinary graded Laurent seed and whole compatibility

Only the assigned ordinary declarations are migrated. There is no auxiliary support T.
Actual original models, selected zero, scalar/null times and seed squares are preserved.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Topology Opposite
open CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open KTheory.Bass CategoryTheory.Functor.IdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.RingedSpace
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]

/-- The actual chosen-zero endomorphism has equal original quotient grades. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientGradedLaurentContraction.lean:33"
  "adaptation" "Original ordinary graded seed, whole Laurent contraction and complete seed squares"]
theorem boundedAboveFlatCoefficientGradedLaurentZero_weak (a : Under R)
    (S : ((boundedAboveFlatCoefficientGradedOpenModelFunctor f).obj a).obj.Obj) :
    ((boundedAboveFlatCoefficientGradedOpenModelFunctor f).obj
      ((laurentUnderFunctor R).obj a)).obj.waldhausen.weq
      ((zeroEndotransformation ((boundedAboveFlatCoefficientGradedOpenModelFunctor f).map
        ((laurentUnderCoefficient R).app a))).app S) := rfl

/-- The whole original Laurent-action contraction has its same scalar and point endpoints. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientGradedLaurentContraction.lean:41"
  "adaptation" "Original ordinary graded seed, whole Laurent contraction and complete seed squares"]
def boundedAboveFlatCoefficientGradedLaurentContraction (a : Under R) :=
  (boundedAboveFlatCoefficientGradedOpenLaurentAction f).contraction
    (boundedAboveFlatCoefficientGradedLaurentZero_weak f) a

/-- The same chosen contraction preserves both independent times under every coefficient map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientGradedLaurentContraction.lean:46"
  "adaptation" "Original ordinary graded seed, whole Laurent contraction and complete seed squares"]
theorem boundedAboveFlatCoefficientGradedLaurentContraction_naturality
    {a b : Under R} (g : a ⟶ b) (n : ℕ) (r t : unitInterval)
    (x : ((boundedAboveFlatCoefficientGradedOpenPrespectrumFunctor f).obj a).space n) :
    ((boundedAboveFlatCoefficientGradedOpenPrespectrumFunctor f).map
      ((laurentUnderFunctor R).map g)).map n
        ((boundedAboveFlatCoefficientGradedLaurentContraction f a).level n (r, (t, x))) =
      (boundedAboveFlatCoefficientGradedLaurentContraction f b).level n
        (r, (t, ((boundedAboveFlatCoefficientGradedOpenPrespectrumFunctor f).map g).map n x)) :=
  (boundedAboveFlatCoefficientGradedOpenLaurentAction f).contraction_naturality
    (boundedAboveFlatCoefficientGradedLaurentZero_weak f) g n r t x

/-- The original graded seed is null through its prescribed original source-leg conjugation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientGradedLaurentContraction.lean:58"
  "adaptation" "Original ordinary graded seed, whole Laurent contraction and complete seed squares"]
def boundedAboveFlatCoefficientGradedOpenBassSeedNull (a : Under R) :
    LoopPrespectrum.Homotopy (boundedAboveFlatCoefficientGradedOpenBassSeedMap f a)
      (zeroHom ((boundedAboveFlatCoefficientGradedOpenPrespectrumFunctor f).obj a)
        (parameterLooping (boundedAboveFlatCoefficientGradedOpenBassCone f a))) :=
  (boundedAboveFlatCoefficientGradedOpenLaurentAction f).seedNullHomotopy
    (boundedAboveFlatCoefficientGradedLaurentZero_weak f) a

/-- The whole original graded seed null is coefficient-natural, with its actual Bass target. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientGradedLaurentContraction.lean:66"
  "adaptation" "Original ordinary graded seed, whole Laurent contraction and complete seed squares"]
def boundedAboveFlatCoefficientGradedOpenBassSeedDiagramNull :
    DiagramNullHomotopy (boundedAboveFlatCoefficientGradedOpenBassSeed f)
      (𝟙 ((strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (boundedAboveFlatCoefficientGradedOpenPrespectrumFunctor f))) :=
  (boundedAboveFlatCoefficientGradedOpenLaurentAction f).seedDiagramNull
    (boundedAboveFlatCoefficientGradedLaurentZero_weak f)

/-- The endpoint cast retains the same original graded seed-null time and loop value. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientGradedLaurentContraction.lean:74"
  "adaptation" "Original ordinary graded seed, whole Laurent contraction and complete seed squares"]
theorem boundedAboveFlatCoefficientGradedOpenBassSeedDiagramNull_level (a : Under R)
    (n : ℕ) (r : unitInterval)
    (x : ((boundedAboveFlatCoefficientGradedOpenPrespectrumFunctor f).obj a).space n) :
    ((boundedAboveFlatCoefficientGradedOpenBassSeedDiagramNull f).homotopy a).level n (r, x) =
      (boundedAboveFlatCoefficientGradedOpenBassSeedNull f a).level n (r, x) := rfl

end AlgebraicGeometry.Scheme.Modules
