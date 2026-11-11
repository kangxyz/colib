import Colib.AlgebraicGeometry.Scheme.GlobalSupportedParameterGeometry

noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.GlobalSupportedParameter
universe u

variable {P Q S T : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

example : baseProductFunctor (specULiftZIsTerminal.from P) ⟶
    baseProductFunctor (specULiftZIsTerminal.from Q) := openTransformation f

example : Scheme.OpenPairs.{u} := pair f S

example (g : S ⟶ T) : pair f S ⟶ pair f T := pairMap f g

example : Scheme.{u} ⥤ Scheme.OpenPairs.{u} := pairs f

example (g : S ⟶ T) :
    (pairMap f g).right = (baseProductFunctor (specULiftZIsTerminal.from Q)).map g :=
  pairMap_right f g

example (g : S ⟶ T) :
    (pairMap f g).left = (baseProductFunctor (specULiftZIsTerminal.from P)).map g :=
  pairMap_left f g
