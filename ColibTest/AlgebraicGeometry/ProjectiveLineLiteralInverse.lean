module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.FlasqueLiteralLaws

set_option autoImplicit false

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

example (X : Scheme.{u}) [CompactSpace X] (n : ℕ) :
    (X.projectiveLineFlasqueCoefficientPair n).comp (X.projectiveLineFlasqueKMap n) =
      MonoidHom.id
        ((FlasquePerfect.waldhausen X).K n × (FlasquePerfect.waldhausen X).K n) :=
  X.projectiveLineFlasqueCoefficientPair_comp n

example (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    (X.projectiveLineFlasqueKMap 0).comp (X.projectiveLineFlasqueCoefficientPair 0) =
      MonoidHom.id ((FlasquePerfect.waldhausen (projectiveSpaceOver 1 X)).K 0) :=
  X.projectiveLineFlasqueKMap_comp_coefficientPair 0

#print axioms AlgebraicGeometry.Scheme.projectiveLineFlasqueKMap_inclusion
#print axioms AlgebraicGeometry.Scheme.projectiveLineFlasqueCoefficientPair_inclusion
#print axioms AlgebraicGeometry.Scheme.projectiveLineFlasqueCoefficientPair_comp
#print axioms AlgebraicGeometry.Scheme.projectiveLineFlasqueKMap_comp_coefficientPair
