module
import Colib.AlgebraicGeometry.Modules.BoundedFlatParameterAuxiliarySupportMaps
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)
example : fiber f T ⟶ ambient T := enlargement f T
example : ambient T ⟶ openModel f T := restriction f T
example : enlargement f T ≫ ParameterModels.forget T.ι =
    ParameterModels.forget (unionOpen f T).ι := enlargement_forget f T
example : restriction f T ≫ ParameterModels.forget (inverseOpen f T).ι =
    ParameterModels.forget T.ι ≫ ambientMap f := restriction_forget f T
example {A B : Scheme.OpenPairs.{u}} (g : A ⟶ B) :
    supportedMap g ≫ ParameterModels.forget A.hom =
      ParameterModels.forget B.hom ≫ ambientMap g.right := supportedMap_forget g
end AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
