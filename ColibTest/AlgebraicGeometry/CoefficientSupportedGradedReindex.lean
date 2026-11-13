module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedGradedReindex

open CategoryTheory AlgebraicGeometry Opposite Topology
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens) [CompactSpace P.left] [CompactSpace Q.left]

example {a b : Under R} (g : a ⟶ b)
    (S : BoundedAboveFlatCoefficientSupportedOpenSections f T a) :
    boundedAboveFlatCoefficientSupportedOpenImageMap f T g
      ((boundedAboveFlatCoefficientSupportedFullOpenGrading f T a).value S) =
    (boundedAboveFlatCoefficientSupportedFullOpenGrading f T b).value
      ((boundedAboveFlatCoefficientSupportedOpenMap f T g).obj S) :=
  boundedAboveFlatCoefficientSupportedOpenImageMap_value f T g S

example {a b : Under R} (g : a ⟶ b) :
    IsExact (boundedAboveFlatCoefficientSupportedFullOpenGrading f T a).coarseStructure.cof
      (boundedAboveFlatCoefficientSupportedFullOpenGrading f T a).coarseStructure.weq
      (boundedAboveFlatCoefficientSupportedFullOpenGrading f T b).coarseStructure.cof
      (boundedAboveFlatCoefficientSupportedFullOpenGrading f T b).coarseStructure.weq
      (boundedAboveFlatCoefficientSupportedOpenMap f T g) :=
  boundedAboveFlatCoefficientSupportedGradedOpenSectionsMap_exact f T g

example {a b : Under R} (g : a ⟶ b) :
    ((boundedAboveFlatCoefficientSupportedGradedOpenModelFunctor f T).map g).hom.toFunctor =
      boundedAboveFlatCoefficientSupportedOpenMap f T g := rfl

example {a b : Under R} (g : a ⟶ b) :
    (boundedAboveFlatCoefficientSupportedFullOpenModelFunctor f T).map g ≫
        (boundedAboveFlatCoefficientSupportedOpenGradingModelTransformation f T).app b =
      (boundedAboveFlatCoefficientSupportedOpenGradingModelTransformation f T).app a ≫
        (boundedAboveFlatCoefficientSupportedGradedOpenModelFunctor f T).map g :=
  (boundedAboveFlatCoefficientSupportedOpenGradingModelTransformation f T).naturality g

example (a : Under R) :
    (boundedAboveFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T).obj a =
      prespectrum (boundedAboveFlatCoefficientSupportedGradedOpenModel f T a) := rfl

example (a : Under R) :
    (boundedAboveFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T).app a =
      prespectrumMap (boundedAboveFlatCoefficientSupportedOpenGradingModelMap f T a) := rfl
