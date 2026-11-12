/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalAuxiliaryParameterCoefficientTrack
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalAuxiliaryParameterFiniteComparison
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeCoefficientSeedNaturality


/-! # The original auxiliary G7 seeds under the actual complete integral Spec square -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient
open GlobalSectionChangeIndex GlobalSupportedSection ParameterLaurentTrack GeometricSeedCospan

/-- The complete actual affine index square followed by a specified original row map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientSeed.lean:28"
  "adaptation" "Actual auxiliary Spec Laurent units, all track times and complete seed squares"]
def rowSquareComparison (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{u + 1})
    (G : Under (CommRingCat.of (ULift.{u} ℤ)) ⥤ LoopPrespectrum.{u + 1})
    (ρ : specUnder ⋙ F ⟶ G) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :=
  F.mapArrow.mapArrow.map (specSquareIso a).hom ≫
    diagramSquareMap ρ (laurentUnderSquare _ a)

/-- Its source corner retains the original whole row map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientSeed.lean:35"
  "adaptation" "Actual auxiliary Spec Laurent units, all track times and complete seed squares"]
theorem rowSquareComparison_source (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{u + 1})
    (G : Under (CommRingCat.of (ULift.{u} ℤ)) ⥤ LoopPrespectrum.{u + 1})
    (ρ : specUnder ⋙ F ⟶ G) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (rowSquareComparison F G ρ a).left.left = ρ.app a := by
  change F.map (𝟙 _) ≫ ρ.app a = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- Its Laurent corner is the exact original composite Model map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientSeed.lean:43"
  "adaptation" "Actual auxiliary Spec Laurent units, all track times and complete seed squares"]
theorem rowSquareComparison_laurent (F : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{u + 1})
    (G : Under (CommRingCat.of (ULift.{u} ℤ)) ⥤ WideSubcategory preservesZero.{u + 1})
    (ρ : specUnder ⋙ F ⟶ G) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (rowSquareComparison (F ⋙ prespectrumFunctor) (G ⋙ prespectrumFunctor)
      (Functor.whiskerRight ρ prespectrumFunctor) a).right.right =
      prespectrumMap (F.map (laurentSpecIso a.right).hom.op ≫
        ρ.app ((laurentUnderFunctor _).obj a)) := by
  change prespectrumFunctor.map _ ≫ prespectrumFunctor.map _ = _
  exact (prespectrumFunctor.map_comp _ _).symm

/-- The first Bass comparison retains the exact square cone and independent loop parameter. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientSeed.lean:54"
  "adaptation" "Actual auxiliary Spec Laurent units, all track times and complete seed squares"]
def rowBassComparison (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{u + 1})
    (G : Under (CommRingCat.of (ULift.{u} ℤ)) ⥤ LoopPrespectrum.{u + 1})
    (ρ : specUnder ⋙ F ⟶ G) :=
  (StrictDiagramIndexChange.iso specUnder (laurentUnderSquareFunctor _)
    squareFunctor specSquare F).hom ≫ (strictDiagramFunctor (laurentUnderSquareFunctor _)).map ρ

/-- The first comparison is literally the map of the complete original square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientSeed.lean:61"
  "adaptation" "Actual auxiliary Spec Laurent units, all track times and complete seed squares"]
theorem rowBassComparison_app (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{u + 1})
    (G : Under (CommRingCat.of (ULift.{u} ℤ)) ⥤ LoopPrespectrum.{u + 1})
    (ρ : specUnder ⋙ F ⟶ G) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (rowBassComparison F G ρ).app a =
      strictSquareLoopedConeFunctor.map (rowSquareComparison F G ρ a) := by
  exact (strictSquareLoopedConeFunctor.map_comp
    (F.mapArrow.mapArrow.map (specSquareIso a).hom)
    (diagramSquareMap ρ (laurentUnderSquare _ a))).symm

variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- The actual ambient seed keeps the original scalar/null word through the full Spec square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientSeed.lean:74"
  "adaptation" "Actual auxiliary Spec Laurent units, all track times and complete seed squares"]
theorem ambient_seed_square (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (T : Q.left.Opens) :
    Functor.whiskerLeft specUnder
        (SchemeNaturalSeed.seed (supportedTrack (T).ι)) ≫
        rowBassComparison (ParameterAuxiliarySupport.ambient T ⋙ prespectrumFunctor)
          (boundedAboveFlatCoefficientSupportedAmbientModelFunctor T ⋙ prespectrumFunctor)
          (Functor.whiskerRight (ambientComparison Q T) prespectrumFunctor) =
      Functor.whiskerRight (ambientComparison Q T) prespectrumFunctor ≫
        (boundedAboveFlatCoefficientSupportedAmbientLaurentAction (Q := Q) T).track.seed := by
  apply NatTrans.ext
  funext a
  rw [NatTrans.comp_app, NatTrans.comp_app, rowBassComparison_app]
  change (SchemeNaturalSeed.seed (supportedTrack (T).ι)).app
      (specUnder.obj a) ≫ strictSquareLoopedConeFunctor.map _ = _
  rw [SchemeCoefficientSeedNaturality.seed_naturality
    (supportedTrack (T).ι)
      (boundedAboveFlatCoefficientSupportedAmbientLaurentAction (Q := Q) T).track
      (specUnder.obj a) a _ (by
      intro n r x
      rw [rowSquareComparison_source, rowSquareComparison_laurent]
      exact ambient_track_square Q T a n r x)]
  rw [rowSquareComparison_source]

/-- The actual fiber seed keeps the original scalar/null word through the full Spec square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientSeed.lean:98"
  "adaptation" "Actual auxiliary Spec Laurent units, all track times and complete seed squares"]
theorem fiber_seed_square :
    Functor.whiskerLeft specUnder
        (SchemeNaturalSeed.seed (supportedTrack (T ⊔ f.left.opensRange).ι)) ≫
        rowBassComparison (ParameterAuxiliarySupport.fiber f.left T ⋙ prespectrumFunctor)
          (boundedAboveFlatCoefficientSupportedFiberModelFunctor f T ⋙ prespectrumFunctor)
          (Functor.whiskerRight (fiberComparison f T) prespectrumFunctor) =
      Functor.whiskerRight (fiberComparison f T) prespectrumFunctor ≫
        (boundedAboveFlatCoefficientSupportedFiberLaurentAction f T).track.seed := by
  apply NatTrans.ext
  funext a
  rw [NatTrans.comp_app, NatTrans.comp_app, rowBassComparison_app]
  change (SchemeNaturalSeed.seed (supportedTrack (T ⊔ f.left.opensRange).ι)).app
      (specUnder.obj a) ≫ strictSquareLoopedConeFunctor.map _ = _
  rw [SchemeCoefficientSeedNaturality.seed_naturality
    (supportedTrack (T ⊔ f.left.opensRange).ι)
      (boundedAboveFlatCoefficientSupportedFiberLaurentAction f T).track
      (specUnder.obj a) a _ (by
      intro n r x
      rw [rowSquareComparison_source, rowSquareComparison_laurent]
      exact fiber_track_square f T a n r x)]
  rw [rowSquareComparison_source]

omit [IsOpenImmersion f.left] in
/-- The actual open seed keeps the original scalar/null word through the full Spec square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientSeed.lean:122"
  "adaptation" "Actual auxiliary Spec Laurent units, all track times and complete seed squares"]
theorem open_seed_square :
    Functor.whiskerLeft specUnder
        (SchemeNaturalSeed.seed (supportedTrack (f.left ⁻¹ᵁ T).ι)) ≫
        rowBassComparison (ParameterAuxiliarySupport.openModel f.left T ⋙ prespectrumFunctor)
          (boundedAboveFlatCoefficientSupportedFullOpenModelFunctor f T ⋙ prespectrumFunctor)
          (Functor.whiskerRight (openComparison f T) prespectrumFunctor) =
      Functor.whiskerRight (openComparison f T) prespectrumFunctor ≫
        (boundedAboveFlatCoefficientSupportedFullOpenLaurentAction f T).track.seed := by
  apply NatTrans.ext
  funext a
  rw [NatTrans.comp_app, NatTrans.comp_app, rowBassComparison_app]
  change (SchemeNaturalSeed.seed (supportedTrack (f.left ⁻¹ᵁ T).ι)).app
      (specUnder.obj a) ≫ strictSquareLoopedConeFunctor.map _ = _
  rw [SchemeCoefficientSeedNaturality.seed_naturality
    (supportedTrack (f.left ⁻¹ᵁ T).ι)
      (boundedAboveFlatCoefficientSupportedFullOpenLaurentAction f T).track
      (specUnder.obj a) a _ (by
      intro n r x
      rw [rowSquareComparison_source, rowSquareComparison_laurent]
      exact open_track_square f T a n r x)]
  rw [rowSquareComparison_source]

end AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient
