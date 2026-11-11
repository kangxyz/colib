/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterCoefficientUnit
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterCoefficientModels
public import Colib.AlgebraicGeometry.Modules.BoundedFlatParameterSupportedTrack

/-! # The actual original integral Spec-to-fine comparison -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Functor.IdentityAutomorphism
open KTheory.Bass
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient
open GlobalSupportedSection
open GlobalSectionChangeIndex ParameterLaurentUnit
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex

/-- The actual global Model maps satisfy the complete coefficient square strictly. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalParameterCoefficientTrack.lean:30"
  "adaptation" "Actual Spec row, whole original scalar/null seed, finite and telescope maps"]
theorem model_coefficient_square
    (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (ParameterModels.ambient Q.left).map (coefficient.app (specUnder.obj a)) ≫
        boundedAboveFlatGlobalSectionModelFunctor.map (laurentParameterIso Q a).hom.op =
      boundedAboveFlatGlobalSectionModelFunctor.map (canonicalRowIso Q a).hom.op ≫
        (globalRow Q).map ((laurentUnderCoefficient _).app a) := by
  change boundedAboveFlatGlobalSectionModelFunctor.map
      ((baseProductFunctor (specULiftZIsTerminal.from Q.left)).map
        ((baseProductProjection
          (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
            (CommRingCat.of (ULift.{u} ℤ)))).app
          (Spec a.right))).op ≫ boundedAboveFlatGlobalSectionModelFunctor.map (laurentParameterIso
            Q a).hom.op =
    boundedAboveFlatGlobalSectionModelFunctor.map (canonicalRowIso Q a).hom.op ≫
      boundedAboveFlatGlobalSectionModelFunctor.map
        (AlgebraicGeometry.Scheme.BaseChange.Coefficients.laurentProjection Q a).op
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp]
  rw [laurentParameterIso_coefficient]

/-- Spec restriction preserves the actual scalar realization at every native degree and time. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalParameterCoefficientTrack.lean:49"
  "adaptation" "Actual Spec row, whole original scalar/null seed, finite and telescope maps"]
theorem track_square
    (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ) (r : unitInterval)
    (x : (prespectrum ((ParameterModels.ambient Q.left).obj (specUnder.obj a))).space n) :
    (prespectrumMap (boundedAboveFlatGlobalSectionModelFunctor.map (laurentParameterIso Q
      a).hom.op)).map n
        (((ParameterLaurentTrack.ambientTrack Q.left).homotopy (specUnder.obj a)).level n (r, x)) =
      (((globalLaurentAction Q).track.homotopy a).level n
        (r, (prespectrumMap (boundedAboveFlatGlobalSectionModelFunctor.map (canonicalRowIso Q
          a).hom.op)).map n x)) := by
  have h := model_coefficient_square Q a
  exact prespectrumIsoHomotopy_square_apply _ _ _ _ _ _ h
    (onFunctor_whisker_square _ _ _ _ (eqToHom (congrArg (fun k ↦ k.hom.toFunctor) h))
      (ambientUnit Q.left (specUnder.obj a)) (globalLaurentUnit Q a)
      (ambientUnit_preserves Q a).whisker) n r x

end AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient

