/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumComposition
public import Colib.AlgebraicGeometry.Scheme.CoefficientPolynomialLaurentProduct
public import Colib.Topology.Prespectrum.HomotopyPushout
public import Colib.Topology.Prespectrum.HomotopyTransport

/-! # The actual geometric comparison from the polynomial span to the Laurent fiber

The two split composition tracks use the same original Laurent projection.
Reverse the positive-chart track and then follow the inverse-chart track.
The homotopy pushout descends exactly this concatenation with the original
positive and inverse chart pullbacks.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}}

/-- The positive chart retains its original split pullback composition track. -/
def boundedAboveFlatCoefficientLaurentPlusHomotopy (P : Over (Spec R)) (a : Under R) :
    Homotopy (boundedAboveFlatPerfectPullbackPrespectrumMap (laurentProjection P a))
      (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap (laurentPlus P a)) :=
  (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy (laurentPlus P a)
    (polynomialProjection P a)).cast
      (congrArg boundedAboveFlatPerfectPullbackPrespectrumMap (laurentPlus_projection P a)) rfl

/-- The inverse chart retains its own original split pullback composition track. -/
def boundedAboveFlatCoefficientLaurentMinusHomotopy (P : Over (Spec R)) (a : Under R) :
    Homotopy (boundedAboveFlatPerfectPullbackPrespectrumMap (laurentProjection P a))
      (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap (laurentMinus P a)) :=
  (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy (laurentMinus P a)
    (polynomialProjection P a)).cast
      (congrArg boundedAboveFlatPerfectPullbackPrespectrumMap (laurentMinus_projection P a)) rfl

/-- The geometric square goes backward on the positive track and forward on the inverse track. -/
def boundedAboveFlatCoefficientBassSquareHomotopy (P : Over (Spec R)) (a : Under R) :=
  (boundedAboveFlatCoefficientLaurentPlusHomotopy P a).symm.trans
    (boundedAboveFlatCoefficientLaurentMinusHomotopy P a)

/-- Descend the actual two chart pullbacks and their specified cylinder to the Laurent fiber. -/
def boundedAboveFlatCoefficientBassSquareComparison (P : Over (Spec R)) (a : Under R) :=
  HomotopyPushout.desc
    (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (laurentPlus P a))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (laurentMinus P a))
    (boundedAboveFlatCoefficientBassSquareHomotopy P a)

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSectionEvaluationSourceLeg.lean:41-71"
  "adaptation" "Both geometric split chart tracks and the literal polynomial-span descent."]
  boundedAboveFlatCoefficientLaurentPlusHomotopy
  boundedAboveFlatCoefficientLaurentMinusHomotopy
  boundedAboveFlatCoefficientBassSquareHomotopy
  boundedAboveFlatCoefficientBassSquareComparison

end AlgebraicGeometry.Scheme.Modules
