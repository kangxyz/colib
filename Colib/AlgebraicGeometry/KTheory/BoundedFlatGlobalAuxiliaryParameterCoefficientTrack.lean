/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalAuxiliaryParameterLaurentComparison


/-! # Whole original Laurent-action times under the auxiliary Spec comparisons -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Functor.IdentityAutomorphism
open KTheory.Bass
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient
open GlobalSectionChangeIndex GlobalSupportedSection ParameterLaurentTrack

/-- Every actual Model row transformation retains the complete integral coefficient square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientTrack.lean:29"
  "adaptation" "Actual auxiliary Spec Laurent units, all track times and complete seed squares"]
theorem row_coefficient_square (F : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{u + 1})
    (G : Under (CommRingCat.of (ULift.{u} ℤ)) ⥤ WideSubcategory preservesZero.{u + 1})
    (ρ : specUnder ⋙ F ⟶ G) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    F.map (coefficient.app (specUnder.obj a)) ≫
        (F.map (laurentSpecIso a.right).hom.op ≫ ρ.app ((laurentUnderFunctor _).obj a)) =
      ρ.app a ≫ G.map ((laurentUnderCoefficient _).app a) := by
  have hc : coefficient.app (specUnder.obj a) ≫ (laurentSpecIso a.right).hom.op =
      specUnder.map ((laurentUnderCoefficient _).app a) := by
    apply Quiver.Hom.unop_inj
    exact laurentSpecIso_hom_fst a.right
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, hc]
  exact ρ.naturality ((laurentUnderCoefficient _).app a)

variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- All original scalar times and native levels are retained on the ambient row. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientTrack.lean:46"
  "adaptation" "Actual auxiliary Spec Laurent units, all track times and complete seed squares"]
theorem ambient_track_square (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (T : Q.left.Opens)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ) (r : unitInterval)
    (x : (prespectrum ((ParameterAuxiliarySupport.ambient T).obj (specUnder.obj a))).space n) :
    (prespectrumMap (ambientLaurentMap Q T a)).map n
        (((supportedTrack (T).ι).homotopy (specUnder.obj a)).level n (r,x)) =
      (((boundedAboveFlatCoefficientSupportedAmbientLaurentAction (Q := Q) T).track.homotopy
        a).level n
        (r, (prespectrumMap ((ambientComparison Q T).app a)).map n x)) := by
  have h := row_coefficient_square (ParameterAuxiliarySupport.ambient T)
    (boundedAboveFlatCoefficientSupportedAmbientModelFunctor T) (ambientComparison Q T) a
  exact prespectrumIsoHomotopy_square_apply _ _ _ _ _ _ h
    (onFunctor_whisker_square _ _ _ _ (eqToHom (congrArg (fun m => m.hom.toFunctor) h))
      (supportedUnit (T).ι (specUnder.obj a))
      ((boundedAboveFlatCoefficientSupportedAmbientLaurentAction (Q := Q) T).unit a)
      (ambientLaurentMap_unit Q T a).whisker) n r x

/-- All original scalar times and native levels are retained on the fiber row. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientTrack.lean:63"
  "adaptation" "Actual auxiliary Spec Laurent units, all track times and complete seed squares"]
theorem fiber_track_square
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ) (r : unitInterval)
    (x : (prespectrum ((ParameterAuxiliarySupport.fiber f.left T).obj (specUnder.obj a))).space n) :
    (prespectrumMap (fiberLaurentMap f T a)).map n
        (((supportedTrack (T ⊔ f.left.opensRange).ι).homotopy (specUnder.obj a)).level n (r,x)) =
      (((boundedAboveFlatCoefficientSupportedFiberLaurentAction f T).track.homotopy a).level n
        (r, (prespectrumMap ((fiberComparison f T).app a)).map n x)) := by
  have h := row_coefficient_square (ParameterAuxiliarySupport.fiber f.left T)
    (boundedAboveFlatCoefficientSupportedFiberModelFunctor f T) (fiberComparison f T) a
  exact prespectrumIsoHomotopy_square_apply _ _ _ _ _ _ h
    (onFunctor_whisker_square _ _ _ _ (eqToHom (congrArg (fun m => m.hom.toFunctor) h))
      (supportedUnit (T ⊔ f.left.opensRange).ι (specUnder.obj a))
      ((boundedAboveFlatCoefficientSupportedFiberLaurentAction f T).unit a)
      (fiberLaurentMap_unit f T a).whisker) n r x

omit [IsOpenImmersion f.left] in
/-- All original scalar times and native levels are retained on the open row. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientTrack.lean:80"
  "adaptation" "Actual auxiliary Spec Laurent units, all track times and complete seed squares"]
theorem open_track_square
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ) (r : unitInterval)
    (x : (prespectrum ((ParameterAuxiliarySupport.openModel f.left T).obj
      (specUnder.obj a))).space n) :
    (prespectrumMap (openLaurentMap f T a)).map n
        (((supportedTrack (f.left ⁻¹ᵁ T).ι).homotopy (specUnder.obj a)).level n (r,x)) =
      (((boundedAboveFlatCoefficientSupportedFullOpenLaurentAction f T).track.homotopy a).level n
        (r, (prespectrumMap ((openComparison f T).app a)).map n x)) := by
  have h := row_coefficient_square (ParameterAuxiliarySupport.openModel f.left T)
    (boundedAboveFlatCoefficientSupportedFullOpenModelFunctor f T) (openComparison f T) a
  exact prespectrumIsoHomotopy_square_apply _ _ _ _ _ _ h
    (onFunctor_whisker_square _ _ _ _ (eqToHom (congrArg (fun m => m.hom.toFunctor) h))
      (supportedUnit (f.left ⁻¹ᵁ T).ι (specUnder.obj a))
      ((boundedAboveFlatCoefficientSupportedFullOpenLaurentAction f T).unit a)
      (openLaurentMap_unit f T a).whisker) n r x

end AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient
