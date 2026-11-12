module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalAuxiliaryParameterCoefficientSeed

open CategoryTheory AlgebraicGeometry Opposite Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
open AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Functor.IdentityAutomorphism
open KTheory.Bass ParameterLaurentTrack ParameterLaurentUnit GeometricSeedCospan
open CommRingCat.PolynomialLaurent
noncomputable section
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)

example (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{u + 1})
    (G : Under (CommRingCat.of (ULift.{u} ℤ)) ⥤ LoopPrespectrum.{u + 1})
    (ρ : specUnder ⋙ F ⟶ G) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (rowSquareComparison F G ρ a).left.left = ρ.app a :=
  rowSquareComparison_source F G ρ a

example (F : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{u + 1})
    (G : Under (CommRingCat.of (ULift.{u} ℤ)) ⥤ WideSubcategory preservesZero.{u + 1})
    (ρ : specUnder ⋙ F ⟶ G) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (rowSquareComparison (F ⋙ prespectrumFunctor) (G ⋙ prespectrumFunctor)
      (Functor.whiskerRight ρ prespectrumFunctor) a).right.right =
      prespectrumMap (F.map (laurentSpecIso a.right).hom.op ≫
        ρ.app ((laurentUnderFunctor _).obj a)) :=
  rowSquareComparison_laurent F G ρ a

example (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{u + 1})
    (G : Under (CommRingCat.of (ULift.{u} ℤ)) ⥤ LoopPrespectrum.{u + 1})
    (ρ : specUnder ⋙ F ⟶ G) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (rowBassComparison F G ρ).app a =
      strictSquareLoopedConeFunctor.map (rowSquareComparison F G ρ a) :=
  rowBassComparison_app F G ρ a

example (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (T : Q.left.Opens) :
    Functor.whiskerLeft specUnder
        (SchemeNaturalSeed.seed (supportedTrack (T).ι)) ≫
        rowBassComparison (ParameterAuxiliarySupport.ambient T ⋙ prespectrumFunctor)
          (boundedAboveFlatCoefficientSupportedAmbientModelFunctor T ⋙ prespectrumFunctor)
          (Functor.whiskerRight (ambientComparison Q T) prespectrumFunctor) =
      Functor.whiskerRight (ambientComparison Q T) prespectrumFunctor ≫
        (boundedAboveFlatCoefficientSupportedAmbientLaurentAction (Q := Q) T).track.seed :=
  ambient_seed_square Q T

example :
    Functor.whiskerLeft specUnder
        (SchemeNaturalSeed.seed (supportedTrack (T ⊔ f.left.opensRange).ι)) ≫
        rowBassComparison (ParameterAuxiliarySupport.fiber f.left T ⋙ prespectrumFunctor)
          (boundedAboveFlatCoefficientSupportedFiberModelFunctor f T ⋙ prespectrumFunctor)
          (Functor.whiskerRight (fiberComparison f T) prespectrumFunctor) =
      Functor.whiskerRight (fiberComparison f T) prespectrumFunctor ≫
        (boundedAboveFlatCoefficientSupportedFiberLaurentAction f T).track.seed :=
  fiber_seed_square f T

example :
    Functor.whiskerLeft specUnder
        (SchemeNaturalSeed.seed (supportedTrack (f.left ⁻¹ᵁ T).ι)) ≫
        rowBassComparison (ParameterAuxiliarySupport.openModel f.left T ⋙ prespectrumFunctor)
          (boundedAboveFlatCoefficientSupportedFullOpenModelFunctor f T ⋙ prespectrumFunctor)
          (Functor.whiskerRight (openComparison f T) prespectrumFunctor) =
      Functor.whiskerRight (openComparison f T) prespectrumFunctor ≫
        (boundedAboveFlatCoefficientSupportedFullOpenLaurentAction f T).track.seed :=
  open_seed_square f T

example (F : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{u + 1})
    (G : Under (CommRingCat.of (ULift.{u} ℤ)) ⥤ WideSubcategory preservesZero.{u + 1})
    (ρ : specUnder ⋙ F ⟶ G) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    F.map (coefficient.app (specUnder.obj a)) ≫
        (F.map (laurentSpecIso a.right).hom.op ≫ ρ.app ((laurentUnderFunctor _).obj a)) =
      ρ.app a ≫ G.map ((laurentUnderCoefficient _).app a) :=
  row_coefficient_square F G ρ a

example (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (T : Q.left.Opens)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ) (r : unitInterval)
    (x : (prespectrum ((ParameterAuxiliarySupport.ambient T).obj (specUnder.obj a))).space n) :
    (prespectrumMap (ambientLaurentMap Q T a)).map n
        (((supportedTrack (T).ι).homotopy (specUnder.obj a)).level n (r,x)) =
      (((boundedAboveFlatCoefficientSupportedAmbientLaurentAction (Q := Q) T).track.homotopy
        a).level n
        (r, (prespectrumMap ((ambientComparison Q T).app a)).map n x)) :=
  ambient_track_square Q T a n r x

example
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ) (r : unitInterval)
    (x : (prespectrum ((ParameterAuxiliarySupport.fiber f.left T).obj (specUnder.obj a))).space n) :
    (prespectrumMap (fiberLaurentMap f T a)).map n
        (((supportedTrack (T ⊔ f.left.opensRange).ι).homotopy (specUnder.obj a)).level n (r,x)) =
      (((boundedAboveFlatCoefficientSupportedFiberLaurentAction f T).track.homotopy a).level n
        (r, (prespectrumMap ((fiberComparison f T).app a)).map n x)) :=
  fiber_track_square f T a n r x

example
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ) (r : unitInterval)
    (x : (prespectrum ((ParameterAuxiliarySupport.openModel f.left T).obj
      (specUnder.obj a))).space n) :
    (prespectrumMap (openLaurentMap f T a)).map n
        (((supportedTrack (f.left ⁻¹ᵁ T).ι).homotopy (specUnder.obj a)).level n (r,x)) =
      (((boundedAboveFlatCoefficientSupportedFullOpenLaurentAction f T).track.homotopy a).level n
        (r, (prespectrumMap ((openComparison f T).app a)).map n x)) :=
  open_track_square f T a n r x

example (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    Preserves (nativeLaurentMap Q a).hom.toFunctor
      (ambientUnit Q.left (specUnder.obj a)) (boundedAboveFlatCoefficientSectionLaurentUnitIso Q
        a) :=
  nativeLaurentMap_unit Q a

example
    (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) (T : Q.left.Opens)
    (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (U : (space (op Q, (laurentUnderFunctor _).obj a)).Opens)
    (m : (ParameterModels.supported T.ι).obj
        (GlobalIndex.laurent.op.obj (specUnder.obj a)) ⟶
      boundedAboveFlatCoefficientSupportedSectionModel
        (i := (op Q, (laurentUnderFunctor _).obj a)) U.ι)
    (h : m.hom.toFunctor ⋙ (boundedAboveFlatCoefficientSectionSupported
        (i := (op Q, (laurentUnderFunctor _).obj a)) U.ι).ι =
      ((ParameterModels.forget T.ι).app
        (GlobalIndex.laurent.op.obj (specUnder.obj a))).hom.toFunctor ⋙
          (nativeLaurentMap Q a).hom.toFunctor) :
    Preserves m.hom.toFunctor (supportedUnit T.ι (specUnder.obj a))
      (boundedAboveFlatCoefficientSupportSectionUnitIso
        (i := (op Q, (laurentUnderFunctor _).obj a)) U.ι (laurentCoordinate a.right)) :=
  supportedLaurentMap_unit Q T a U m h

example
    (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (ParameterModels.ambient Q.left).map (laurentSpecIso a.right).hom.op ≫
      (parameterCoefficientRestriction Q).app ((laurentUnderFunctor _).obj a) =
        nativeLaurentMap Q a :=
  nativeLaurentMap_factor Q a

example
    (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) (T : Q.left.Opens)
    (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (U : (space (op Q, (laurentUnderFunctor _).obj a)).Opens)
    (m : (ParameterModels.supported T.ι).obj
        (specUnder.obj ((laurentUnderFunctor _).obj a)) ⟶
      boundedAboveFlatCoefficientSupportedSectionModel
        (i := (op Q, (laurentUnderFunctor _).obj a)) U.ι)
    (h : m.hom.toFunctor ⋙ (boundedAboveFlatCoefficientSectionSupported
        (i := (op Q, (laurentUnderFunctor _).obj a)) U.ι).ι =
      ((ParameterModels.forget T.ι).app
        (specUnder.obj ((laurentUnderFunctor _).obj a))).hom.toFunctor ⋙
          ((parameterCoefficientRestriction Q).app ((laurentUnderFunctor _).obj a)).hom.toFunctor) :
    ((ParameterModels.supported T.ι).map (laurentSpecIso a.right).hom.op ≫ m).hom.toFunctor ⋙
      (boundedAboveFlatCoefficientSectionSupported
        (i := (op Q, (laurentUnderFunctor _).obj a)) U.ι).ι =
    ((ParameterModels.forget T.ι).app
      (GlobalIndex.laurent.op.obj (specUnder.obj a))).hom.toFunctor ⋙
        (nativeLaurentMap Q a).hom.toFunctor :=
  laurentComponent_forget Q T a U m h

example (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (T : Q.left.Opens)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    Preserves (ambientLaurentMap Q T a).hom.toFunctor
      (supportedUnit (T).ι (specUnder.obj a))
      (boundedAboveFlatCoefficientSupportedAmbientLaurentUnitIso Q T a) :=
  ambientLaurentMap_unit Q T a

example
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    Preserves (fiberLaurentMap f T a).hom.toFunctor
      (supportedUnit (T ⊔ f.left.opensRange).ι (specUnder.obj a))
      (boundedAboveFlatCoefficientSupportedFiberLaurentUnitIso f T a) :=
  fiberLaurentMap_unit f T a

example
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    Preserves (openLaurentMap f T a).hom.toFunctor
      (supportedUnit (f.left ⁻¹ᵁ T).ι (specUnder.obj a))
      (boundedAboveFlatCoefficientSupportedFullOpenLaurentUnitIso f T a) :=
  openLaurentMap_unit f T a

