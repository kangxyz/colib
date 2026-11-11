module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryOpenNull
@[expose] public noncomputable section
open Topology CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
universe u
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]
example (a : Under R) (S : BoundedAboveFlatCoefficientSections (Opposite.op Q, a)) :
    (boundedAboveFlatCoefficientGradedOpenModel f a).obj.waldhausen.weq
      ((boundedAboveFlatCoefficientOpenZeroToGraded f a).app S) :=
  boundedAboveFlatCoefficientOpenZeroToGraded_weak f a S
variable [CompactSpace P.left] [CompactSpace Q.left]
example {a b : Under R} (g : a ⟶ b) (n : ℕ) (s : unitInterval)
    (x : ((boundedAboveFlatCoefficientOpenPrespectrumFunctor f).obj a).space n) :
    ((boundedAboveFlatCoefficientGradedOpenPrespectrumFunctor f).map g).map n
        (((boundedAboveFlatCoefficientOpenGradingDiagramNull f).homotopy a).level n (s, x)) =
      ((boundedAboveFlatCoefficientOpenGradingDiagramNull f).homotopy b).level n
        (s, ((boundedAboveFlatCoefficientOpenPrespectrumFunctor f).map g).map n x) :=
  boundedAboveFlatCoefficientOpenGradingDiagramNull_coefficient f g n s x
