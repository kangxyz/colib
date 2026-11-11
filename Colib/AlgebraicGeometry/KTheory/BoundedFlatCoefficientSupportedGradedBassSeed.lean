/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedOpenBassSeed
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedGradedReindex
public import Colib.RingTheory.KTheory.Bass.StrictLaurentSeedContraction




/-!
# Original auxiliary-supported coefficient Laurent actions and Bass seeds

Forward native coefficient units lift through the actual supported section
inclusions. Their original coefficient and restriction equations prove the
supported C_Z/F_Z/G_Z action tracks and seeds with the same square, joint zero,
source-leg cylinder and scalar/null concatenation. Equal endpoint grades make
the actual graded zero endomorphism weak and construct the complete graded
seed contraction. Only the G_Z coefficient diagram requires compact P and Q.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology Opposite
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open KTheory.Bass CategoryTheory.Functor.IdentityAutomorphism
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.RingedSpace
variable {R : CommRingCat.{u}}
attribute [local irreducible] boundedAboveFlatCoefficientOriginalEvaluation
  boundedAboveFlatPerfectGlobalUnitIso boundedAboveFlatCoefficientSectionLaurentUnitIso

variable {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)

variable [CompactSpace P.left] [CompactSpace Q.left]

/-- The same actual open unit acts on the original graded Model; only weakness changes. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenBassSeed.lean:114"
  "adaptation" "Original graded Laurent action, full seed contraction and independent null times"]
def boundedAboveFlatCoefficientSupportedGradedOpenLaurentAction :
    LaurentSeed.ModelAction (boundedAboveFlatCoefficientSupportedGradedOpenModelFunctor f T) where
  unit a := boundedAboveFlatCoefficientSupportedFullOpenLaurentUnitIso f T a
  naturality g := boundedAboveFlatCoefficientSupportedFullOpenLaurentUnitIso_coefficient f T g

/-- The unchanged forward Laurent unit realized in the original graded coefficient diagram. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenBassSeed.lean:120"
  "adaptation" "Original graded Laurent action, full seed contraction and independent null times"]
def boundedAboveFlatCoefficientSupportedGradedOpenLaurentHomotopy (a : Under R) :=
  (boundedAboveFlatCoefficientSupportedGradedOpenLaurentAction f T).track.homotopy a

/-- The original graded native four-corner square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenBassSeed.lean:124"
  "adaptation" "Original graded Laurent action, full seed contraction and independent null times"]
def boundedAboveFlatCoefficientSupportedGradedOpenBassSquare (a : Under R) :=
  LaurentSeed.square (boundedAboveFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T) a

/-- The actual mapping cone of the original graded comparison map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenBassSeed.lean:128"
  "adaptation" "Original graded Laurent action, full seed contraction and independent null times"]
def boundedAboveFlatCoefficientSupportedGradedOpenBassCone (a : Under R) :=
  LaurentSeed.cone (boundedAboveFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T) a

/-- The original graded source-leg cylinder, with every time parameter unchanged. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenBassSeed.lean:132"
  "adaptation" "Original graded Laurent action, full seed contraction and independent null times"]
def boundedAboveFlatCoefficientSupportedGradedOpenBassNullHomotopy (a : Under R) :=
  LaurentSeed.sourceNull (boundedAboveFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T) a

/-- The graded pointwise seed uses that original source-leg null and forward scalar action. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenBassSeed.lean:136"
  "adaptation" "Original graded Laurent action, full seed contraction and independent null times"]
def boundedAboveFlatCoefficientSupportedGradedOpenBassSeedMap (a : Under R) :=
  (boundedAboveFlatCoefficientSupportedGradedOpenLaurentAction f T).track.seedMap a

/-- The constructed coefficient-natural original graded Bass seed. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenBassSeed.lean:140"
  "adaptation" "Original graded Laurent action, full seed contraction and independent null times"]
def boundedAboveFlatCoefficientSupportedGradedOpenBassSeed :
    boundedAboveFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T ⟶
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (boundedAboveFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T) :=
  (boundedAboveFlatCoefficientSupportedGradedOpenLaurentAction f T).track.seed

/-- The actual chosen-zero endomorphism has equal original quotient grades. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenBassSeed.lean:147"
  "adaptation" "Original graded Laurent action, full seed contraction and independent null times"]
theorem boundedAboveFlatCoefficientSupportedGradedLaurentZero_weak (a : Under R)
    (S : ((boundedAboveFlatCoefficientSupportedGradedOpenModelFunctor f T).obj a).obj.Obj) :
    ((boundedAboveFlatCoefficientSupportedGradedOpenModelFunctor f T).obj
      ((laurentUnderFunctor R).obj a)).obj.waldhausen.weq
      ((zeroEndotransformation ((boundedAboveFlatCoefficientSupportedGradedOpenModelFunctor f T).map
        ((laurentUnderCoefficient R).app a))).app S) := rfl

/-- The whole original Laurent-action contraction has its same scalar and point endpoints. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenBassSeed.lean:155"
  "adaptation" "Original graded Laurent action, full seed contraction and independent null times"]
def boundedAboveFlatCoefficientSupportedGradedLaurentContraction (a : Under R) :=
  (boundedAboveFlatCoefficientSupportedGradedOpenLaurentAction f T).contraction
    (boundedAboveFlatCoefficientSupportedGradedLaurentZero_weak f T) a

/-- The same chosen contraction preserves both independent times under every coefficient map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenBassSeed.lean:160"
  "adaptation" "Original graded Laurent action, full seed contraction and independent null times"]
theorem boundedAboveFlatCoefficientSupportedGradedLaurentContraction_naturality
    {a b : Under R} (g : a ⟶ b) (n : ℕ) (r t : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T).obj a).space n) :
    ((boundedAboveFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T).map
      ((laurentUnderFunctor R).map g)).map n
        ((boundedAboveFlatCoefficientSupportedGradedLaurentContraction f T a).level n (r, (t, x))) =
      (boundedAboveFlatCoefficientSupportedGradedLaurentContraction f T b).level n
        (r, (t, ((boundedAboveFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T).map g).map n
          x)) :=
  (boundedAboveFlatCoefficientSupportedGradedOpenLaurentAction f T).contraction_naturality
    (boundedAboveFlatCoefficientSupportedGradedLaurentZero_weak f T) g n r t x

/-- The original graded seed is null through its prescribed original source-leg conjugation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenBassSeed.lean:173"
  "adaptation" "Original graded Laurent action, full seed contraction and independent null times"]
def boundedAboveFlatCoefficientSupportedGradedOpenBassSeedNull (a : Under R) :
    LoopPrespectrum.Homotopy (boundedAboveFlatCoefficientSupportedGradedOpenBassSeedMap f T a)
      (zeroHom ((boundedAboveFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T).obj a)
        (parameterLooping (boundedAboveFlatCoefficientSupportedGradedOpenBassCone f T a))) :=
  (boundedAboveFlatCoefficientSupportedGradedOpenLaurentAction f T).seedNullHomotopy
    (boundedAboveFlatCoefficientSupportedGradedLaurentZero_weak f T) a

/-- The whole original graded seed null is coefficient-natural, with its actual Bass target. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenBassSeed.lean:181"
  "adaptation" "Original graded Laurent action, full seed contraction and independent null times"]
def boundedAboveFlatCoefficientSupportedGradedOpenBassSeedDiagramNull :
    DiagramNullHomotopy (boundedAboveFlatCoefficientSupportedGradedOpenBassSeed f T)
      (𝟙 ((strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (boundedAboveFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T))) :=
  (boundedAboveFlatCoefficientSupportedGradedOpenLaurentAction f T).seedDiagramNull
    (boundedAboveFlatCoefficientSupportedGradedLaurentZero_weak f T)

/-- The endpoint cast retains the same original graded seed-null time and loop value. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedOpenBassSeed.lean:189"
  "adaptation" "Original graded Laurent action, full seed contraction and independent null times"]
theorem boundedAboveFlatCoefficientSupportedGradedOpenBassSeedDiagramNull_level (a : Under R)
    (n : ℕ) (r : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T).obj a).space n) :
    ((boundedAboveFlatCoefficientSupportedGradedOpenBassSeedDiagramNull f T).homotopy a).level n
      (r, x) =
      (boundedAboveFlatCoefficientSupportedGradedOpenBassSeedNull f T a).level n (r, x) := rfl

end AlgebraicGeometry.Scheme.Modules

