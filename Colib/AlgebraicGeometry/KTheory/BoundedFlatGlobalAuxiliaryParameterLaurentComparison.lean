/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalAuxiliaryParameterCoefficientUnit
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedFiberBassSeed
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedOpenBassSeed


/-! # The three actual Laurent corners and their original forward units -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow
open CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Functor.IdentityAutomorphism
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient
open GlobalSectionChangeIndex GlobalSupportedSection ParameterLaurentTrack

/-- The actual affine Laurent comparison and row restriction form one complete Model map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterLaurentComparison.lean:30"
  "adaptation" "Actual auxiliary Spec Laurent units, all track times and complete seed squares"]
theorem nativeLaurentMap_factor
    (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (ParameterModels.ambient Q.left).map (laurentSpecIso a.right).hom.op ≫
      (parameterCoefficientRestriction Q).app ((laurentUnderFunctor _).obj a) =
        nativeLaurentMap Q a := by
  unfold parameterCoefficientRestriction
  rw [NatTrans.comp_app, parameterRowModelIso_hom_app]
  change boundedAboveFlatGlobalSectionModelFunctor.map _ ≫
    boundedAboveFlatGlobalSectionModelFunctor.map _ ≫
    (rowRestriction Q).app ((laurentUnderFunctor _).obj a) = _
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp]
  rfl

/-- Any actual native support component with the full forget square retains its Laurent corner. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterLaurentComparison.lean:44"
  "adaptation" "Actual auxiliary Spec Laurent units, all track times and complete seed squares"]
theorem laurentComponent_forget
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
        (nativeLaurentMap Q a).hom.toFunctor := by
  have hn := congrArg (fun m => m.hom.toFunctor)
    ((ParameterModels.forget T.ι).naturality (laurentSpecIso a.right).hom.op)
  change ((ParameterModels.supported T.ι).map (laurentSpecIso a.right).hom.op).hom.toFunctor ⋙
      ((ParameterModels.forget T.ι).app
        (specUnder.obj ((laurentUnderFunctor _).obj a))).hom.toFunctor =
    ((ParameterModels.forget T.ι).app
      (GlobalIndex.laurent.op.obj (specUnder.obj a))).hom.toFunctor ⋙
      ((ParameterModels.ambient Q.left).map (laurentSpecIso a.right).hom.op).hom.toFunctor at hn
  have ha := congrArg (fun m => m.hom.toFunctor) (nativeLaurentMap_factor Q a)
  change ((ParameterModels.ambient Q.left).map (laurentSpecIso a.right).hom.op).hom.toFunctor ⋙
      ((parameterCoefficientRestriction Q).app ((laurentUnderFunctor _).obj a)).hom.toFunctor =
    (nativeLaurentMap Q a).hom.toFunctor at ha
  change ((ParameterModels.supported T.ι).map (laurentSpecIso a.right).hom.op).hom.toFunctor ⋙
    m.hom.toFunctor ⋙ (boundedAboveFlatCoefficientSectionSupported
      (i := (op Q, (laurentUnderFunctor _).obj a)) U.ι).ι = _
  rw [h, ← Functor.assoc, hn, Functor.assoc, ha]

variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- The actual ambient Laurent corner uses the same affine index map and original row. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterLaurentComparison.lean:84"
  "adaptation" "Actual auxiliary Spec Laurent units, all track times and complete seed squares"]
def ambientLaurentMap (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (T : Q.left.Opens) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :=
  (ParameterModels.supported (T).ι).map (laurentSpecIso a.right).hom.op ≫
    ambientComponent Q T ((laurentUnderFunctor _).obj a)

/-- The original forward ambient Laurent unit is retained under the complete comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterLaurentComparison.lean:90"
  "adaptation" "Actual auxiliary Spec Laurent units, all track times and complete seed squares"]
theorem ambientLaurentMap_unit (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (T : Q.left.Opens)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    Preserves (ambientLaurentMap Q T a).hom.toFunctor
      (supportedUnit (T).ι (specUnder.obj a))
      (boundedAboveFlatCoefficientSupportedAmbientLaurentUnitIso Q T a) := by
  apply supportedLaurentMap_unit Q (T) a
  exact laurentComponent_forget Q (T) a _ _
    (ambientComponent_forget Q T ((laurentUnderFunctor _).obj a))

/-- The actual fiber Laurent corner uses the same affine index map and original row. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterLaurentComparison.lean:101"
  "adaptation" "Actual auxiliary Spec Laurent units, all track times and complete seed squares"]
def fiberLaurentMap (a : Under (CommRingCat.of (ULift.{u} ℤ))) :=
  (ParameterModels.supported (T ⊔ f.left.opensRange).ι).map (laurentSpecIso a.right).hom.op ≫
    fiberComponent f T ((laurentUnderFunctor _).obj a)

/-- The original forward fiber Laurent unit is retained under the complete comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterLaurentComparison.lean:106"
  "adaptation" "Actual auxiliary Spec Laurent units, all track times and complete seed squares"]
theorem fiberLaurentMap_unit
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    Preserves (fiberLaurentMap f T a).hom.toFunctor
      (supportedUnit (T ⊔ f.left.opensRange).ι (specUnder.obj a))
      (boundedAboveFlatCoefficientSupportedFiberLaurentUnitIso f T a) := by
  apply supportedLaurentMap_unit Q (T ⊔ f.left.opensRange) a
  exact laurentComponent_forget Q (T ⊔ f.left.opensRange) a _ _
    (fiberComponent_forget f T ((laurentUnderFunctor _).obj a))

/-- The actual open Laurent corner uses the same affine index map and original row. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterLaurentComparison.lean:116"
  "adaptation" "Actual auxiliary Spec Laurent units, all track times and complete seed squares"]
def openLaurentMap (a : Under (CommRingCat.of (ULift.{u} ℤ))) :=
  (ParameterModels.supported (f.left ⁻¹ᵁ T).ι).map (laurentSpecIso a.right).hom.op ≫
    openComponent f T ((laurentUnderFunctor _).obj a)

omit [IsOpenImmersion f.left] in
/-- The original forward open Laurent unit is retained under the complete comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterLaurentComparison.lean:122"
  "adaptation" "Actual auxiliary Spec Laurent units, all track times and complete seed squares"]
theorem openLaurentMap_unit
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    Preserves (openLaurentMap f T a).hom.toFunctor
      (supportedUnit (f.left ⁻¹ᵁ T).ι (specUnder.obj a))
      (boundedAboveFlatCoefficientSupportedFullOpenLaurentUnitIso f T a) := by
  apply supportedLaurentMap_unit P (f.left ⁻¹ᵁ T) a
  exact laurentComponent_forget P (f.left ⁻¹ᵁ T) a _ _
    (openComponent_forget f T ((laurentUnderFunctor _).obj a))

end AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient
