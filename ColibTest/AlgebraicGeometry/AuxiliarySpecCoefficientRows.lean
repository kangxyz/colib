module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalAuxiliaryParameterCoefficientRestriction

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
open AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
noncomputable section
universe u
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)

example {a b : Under (CommRingCat.of (ULift.{u} ℤ))} (g : a ⟶ b) :
    (boundedAboveFlatCoefficientSupportedFiberModelMap f T g).hom.toFunctor ⋙
        (boundedAboveFlatCoefficientSectionSupported
          (boundedAboveFlatCoefficientFiberSupportOpen f T b).ι).ι =
      (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientFiberSupportOpen f
        T a).ι).ι ⋙
        ((boundedAboveFlatCoefficientSectionModelRow Q).map g).hom.toFunctor :=
  fineFiberMap_forget f T g

example {a b : Under (CommRingCat.of (ULift.{u} ℤ))}
    (g : a ⟶ b) :
    (ParameterAuxiliarySupport.fiber f.left T).map (specUnder.map g) ≫ fiberComponent f T b =
      fiberComponent f T a ≫ (boundedAboveFlatCoefficientSupportedFiberModelFunctor f T).map g :=
  fiberComponent_naturality f T g

example {a b : Under (CommRingCat.of (ULift.{u} ℤ))} (g : a ⟶ b) :
    (boundedAboveFlatCoefficientSupportedFullOpenModelMap f T g).hom.toFunctor ⋙
        (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientOpenSupportOpen f
          T b).ι).ι =
      (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientOpenSupportOpen f T
        a).ι).ι ⋙
        ((boundedAboveFlatCoefficientSectionModelRow P).map g).hom.toFunctor :=
  fineOpenMap_forget f T g

example {a b : Under (CommRingCat.of (ULift.{u} ℤ))}
    (g : a ⟶ b) :
    (ParameterAuxiliarySupport.openModel f.left T).map (specUnder.map g) ≫ openComponent f T b =
      openComponent f T a ≫ (boundedAboveFlatCoefficientSupportedFullOpenModelFunctor f T).map g :=
  openComponent_naturality f T g

example :
    Functor.whiskerLeft specUnder (ParameterAuxiliarySupport.enlargement f.left T) ≫
        ambientComparison Q T =
      fiberComparison f T ≫ boundedAboveFlatCoefficientSupportedFiberForgetModelTransformation f T
        :=
  enlargement_square f T

example :
    ParameterAuxiliarySupport.ambientMap f.left =
      GlobalParameterCoefficient.parameterFullRestriction f :=
  ambientMap_eq_fullRestriction f

example :
    globalOpenFineRestriction f ≫ rowRestriction P =
      rowRestriction Q ≫ boundedAboveFlatCoefficientSectionModelRestriction f :=
  originalRestriction_square f

example :
    Functor.whiskerLeft specUnder (ParameterAuxiliarySupport.ambientMap f.left) ≫
        parameterCoefficientRestriction P =
      parameterCoefficientRestriction Q ≫ boundedAboveFlatCoefficientSectionModelRestriction f :=
  ambientRestriction_square f

example (T : Q.left.Opens)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    ((boundedAboveFlatCoefficientSupportedOpenChangeWeakModelMap f T a) ≫
        boundedAboveFlatCoefficientSupportedOpenRestrictionModelMap f T a).hom.toFunctor ⋙
      (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientOpenSupportOpen f T
        a).ι).ι =
    (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientSupportOpen Q T
      a).ι).ι ⋙
      ((boundedAboveFlatCoefficientSectionModelRestriction f).app a).hom.toFunctor :=
  fineRestriction_forget f T a

example (T : Q.left.Opens) :
    Functor.whiskerLeft specUnder (ParameterAuxiliarySupport.restriction f.left T) ≫
        openComparison f T =
      ambientComparison Q T ≫
        (boundedAboveFlatCoefficientSupportedOpenChangeWeakModelTransformation f T ≫
          boundedAboveFlatCoefficientSupportedOpenRestrictionModelTransformation f T) :=
  restriction_square f T

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (ambientComponent Q T a).hom.toFunctor ⋙
        (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientSupportOpen Q T
          a).ι).ι =
      ((ParameterModels.forget T.ι).app (specUnder.obj a)).hom.toFunctor ⋙
        ((parameterCoefficientRestriction Q).app a).hom.toFunctor :=
  ambientComponent_forget Q T a

example {a b : Under (CommRingCat.of (ULift.{u} ℤ))} (g : a ⟶ b) :
    (boundedAboveFlatCoefficientSupportedAmbientModelMap T g).hom.toFunctor ⋙
        (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientSupportOpen Q T
          b).ι).ι =
      (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientSupportOpen Q T
        a).ι).ι ⋙
        ((boundedAboveFlatCoefficientSectionModelRow Q).map g).hom.toFunctor :=
  fineAmbientMap_forget Q T g

example {a b : Under (CommRingCat.of (ULift.{u} ℤ))}
    (g : a ⟶ b) :
    (ParameterAuxiliarySupport.ambient T).map (specUnder.map g) ≫ ambientComponent Q T b =
      ambientComponent Q T a ≫ (boundedAboveFlatCoefficientSupportedAmbientModelFunctor T).map g :=
  ambientComponent_naturality Q T g

example {R : CommRingCat.{u}} (c : Index R)
    {A B : (space c).Opens} (h : A = B) :
    (eqToHom (congrArg (fun U : (space c).Opens =>
      boundedAboveFlatCoefficientSupportedSectionModel (i := c) U.ι) h)).hom.toFunctor ⋙
        (boundedAboveFlatCoefficientSectionSupported B.ι).ι =
      (boundedAboveFlatCoefficientSectionSupported A.ι).ι :=
  nativeSupportTransport_forget c h

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (fiberComponent f T a).hom.toFunctor ⋙
        (boundedAboveFlatCoefficientSectionSupported
          (boundedAboveFlatCoefficientFiberSupportOpen f T a).ι).ι =
      ((ParameterModels.forget (T ⊔ f.left.opensRange).ι).app (specUnder.obj a)).hom.toFunctor ⋙
        ((parameterCoefficientRestriction Q).app a).hom.toFunctor :=
  fiberComponent_forget f T a

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (openComponent f T a).hom.toFunctor ⋙
        (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientOpenSupportOpen f
          T a).ι).ι =
      ((ParameterModels.forget (f.left ⁻¹ᵁ T).ι).app (specUnder.obj a)).hom.toFunctor ⋙
        ((parameterCoefficientRestriction P).app a).hom.toFunctor :=
  openComponent_forget f T a

example : specUnder ⋙ ParameterAuxiliarySupport.ambient T ⟶
    boundedAboveFlatCoefficientSupportedAmbientModelFunctor T := ambientComparison Q T

example : specUnder ⋙ ParameterAuxiliarySupport.fiber f.left T ⟶
    boundedAboveFlatCoefficientSupportedFiberModelFunctor f T := fiberComparison f T

example : specUnder ⋙ ParameterAuxiliarySupport.openModel f.left T ⟶
    boundedAboveFlatCoefficientSupportedFullOpenModelFunctor f T := openComparison f T
