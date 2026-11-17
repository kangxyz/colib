module
import Colib.AlgebraicGeometry.Correspondences.Monoidal.NativeParameter
noncomputable section
open CategoryTheory
universe u
variable {k : Type u} [Field k]
example : MonoidalCategory (AlgebraicGeometry.Cor k) := inferInstance
example : SymmetricCategory (AlgebraicGeometry.Cor k) := inferInstance
example : MonoidalPreadditive (AlgebraicGeometry.Cor k) := inferInstance
example : (AlgebraicGeometry.Cor.graphFunctor k).Braided := inferInstance
#print axioms AlgebraicGeometry.Cor.monoidalCategory
#print axioms AlgebraicGeometry.Cor.symmetricCategory
#print axioms AlgebraicGeometry.Cor.monoidalPreadditive
#print axioms AlgebraicGeometry.Cor.graphFunctorBraided
#print axioms AlgebraicGeometry.Cor.tensorRightIsoParameterProduct
#check @AlgebraicGeometry.Cor.tensorRightIsoParameterProduct
