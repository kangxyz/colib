module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryOpenGradingNaturality
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Topology CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.StrictSections AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.Modules
universe u
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
example {a b : Under R} (g : a ⟶ b)
    (S : BoundedAboveFlatCoefficientSections (op P, a)) :
    boundedAboveFlatCoefficientOpenImageMap f g ((boundedAboveFlatCoefficientFullOpenGrading f
      a).value S) =
      (boundedAboveFlatCoefficientFullOpenGrading f b).value
        ((boundedAboveFlatCoefficientSectionsMap
          (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g)).obj S)  :=
  boundedAboveFlatCoefficientOpenImageMap_value f g S

example {a b : Under R} (g : a ⟶ b) :
    IsExact (boundedAboveFlatCoefficientFullOpenGrading f a).coarseStructure.cof
      (boundedAboveFlatCoefficientFullOpenGrading f a).coarseStructure.weq
      (boundedAboveFlatCoefficientFullOpenGrading f b).coarseStructure.cof
      (boundedAboveFlatCoefficientFullOpenGrading f b).coarseStructure.weq
      (boundedAboveFlatCoefficientSectionsMap (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g)) :=
  boundedAboveFlatCoefficientGradedOpenSectionsMap_exact f g

example : boundedAboveFlatCoefficientFullOpenModelFunctor f ⟶
    boundedAboveFlatCoefficientGradedOpenModelFunctor f :=
  boundedAboveFlatCoefficientOpenGradingModelTransformation f
