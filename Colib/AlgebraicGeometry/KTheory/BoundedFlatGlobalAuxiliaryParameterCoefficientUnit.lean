/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalAuxiliaryParameterCoefficientRestriction
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterCoefficientUnit
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSectionLaurentAction
public import Colib.AlgebraicGeometry.Modules.BoundedFlatParameterSupportedTrack
public import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientSupportedUnits


/-! # The actual forward Laurent unit on auxiliary-supported integral comparisons -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow
open CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Functor.IdentityAutomorphism
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient
open GlobalSectionChangeIndex GlobalSupportedSection ParameterLaurentUnit ParameterLaurentTrack

/-- The actual Laurent comparison followed by original coefficient restriction. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientUnit.lean:31"
  "adaptation" "Actual auxiliary Spec Laurent units, all track times and complete seed squares"]
def nativeLaurentMap (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :=
  boundedAboveFlatGlobalSectionModelFunctor.map (laurentParameterIso Q a).hom.op ≫
    (rowRestriction Q).app ((laurentUnderFunctor _).obj a)

/-- This whole original Model map preserves the original forward coefficient Laurent unit. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientUnit.lean:37"
  "adaptation" "Actual auxiliary Spec Laurent units, all track times and complete seed squares"]
theorem nativeLaurentMap_unit (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    Preserves (nativeLaurentMap Q a).hom.toFunctor
      (ambientUnit Q.left (specUnder.obj a)) (boundedAboveFlatCoefficientSectionLaurentUnitIso Q
        a) := by
  intro x
  change ((rowRestriction Q).app ((laurentUnderFunctor _).obj a)).hom.toFunctor.map
      ((boundedAboveFlatGlobalSectionModelFunctor.map (laurentParameterIso Q
        a).hom.op).hom.toFunctor.map
        ((ambientUnit Q.left (specUnder.obj a)).hom.app x)) = _
  rw [GlobalParameterCoefficient.ambientUnit_preserves Q a x]
  exact coefficientRestriction_unit_preserves _ (op Q, (laurentUnderFunctor _).obj a)
    (boundedAboveFlatCoefficientUnit (op Q, (laurentUnderFunctor _).obj a)
      (laurentCoordinate a.right)) _

/-- A proved complete support-forget square transports the actual forward Laurent action. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientUnit.lean:51"
  "adaptation" "Actual auxiliary Spec Laurent units, all track times and complete seed squares"]
theorem supportedLaurentMap_unit
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
        (i := (op Q, (laurentUnderFunctor _).obj a)) U.ι (laurentCoordinate a.right)) := by
  let : (boundedAboveFlatCoefficientSectionSupported
        (i := (op Q, (laurentUnderFunctor _).obj a)) U.ι).ι.Faithful :=
    (boundedAboveFlatCoefficientSectionSupported
        (i := (op Q, (laurentUnderFunctor _).obj a)) U.ι).fullyFaithfulι.faithful
  apply evaluationPreserves_of_eq m.hom.toFunctor
    (boundedAboveFlatCoefficientSectionSupported
        (i := (op Q, (laurentUnderFunctor _).obj a)) U.ι).ι _ h
    (supportedUnit T.ι (specUnder.obj a)) _ (boundedAboveFlatCoefficientSectionLaurentUnitIso Q a)
  · intro x
    change (nativeLaurentMap Q a).hom.toFunctor.map
      (((supportedUnit T.ι (specUnder.obj a)).hom.app x).hom) = _
    rw [show ((supportedUnit T.ι (specUnder.obj a)).hom.app x).hom =
      (ambientUnit Q.left (specUnder.obj a)).hom.app x.obj from
        forget_unit T.ι (specUnder.obj a) x]
    exact nativeLaurentMap_unit Q a x.obj
  · intro x
    exact boundedAboveFlatCoefficientSupportSectionUnitIso_hom
      (i := (op Q, (laurentUnderFunctor _).obj a)) U.ι (laurentCoordinate a.right) x

end AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient
