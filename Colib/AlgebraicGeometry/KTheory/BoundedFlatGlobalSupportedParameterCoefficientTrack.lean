/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSupportedParameterCoefficientUnit

/-!
# Every original supported scalar-track time under integral Spec restriction

The original affine projection square and the supported row naturality give the strict
Model coefficient square. The original unit-preservation theorem then identifies the
complete supported prespectrum homotopy at each degree and scalar time.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Functor.IdentityAutomorphism
open KTheory.Bass
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedParameterCoefficient
open GlobalSectionChangeIndex GlobalSupportedSection ParameterLaurentTrack
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

/-- The complete actual supported coefficient square, before prespectrum realization. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSupportedParameterCoefficientTrack.lean:34"
  "adaptation" "Original supported Spec unit, every track time and actual seed square"]
theorem model_coefficient_square (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (ParameterModels.supported f.left).map (coefficient.app (specUnder.obj a)) ≫
        laurentModelMap f a =
      (parameterSupportedRowIso f).hom.app a ≫
        (supportedRow f).map ((laurentUnderCoefficient _).app a) := by
  have hc : coefficient.app (specUnder.obj a) ≫ (laurentSpecIso a.right).hom.op =
      specUnder.map ((laurentUnderCoefficient _).app a) := by
    apply Quiver.Hom.unop_inj
    exact laurentSpecIso_hom_fst a.right
  rw [laurentModelMap, ← Category.assoc, ← CategoryTheory.Functor.map_comp, hc]
  exact (parameterSupportedRowIso f).hom.naturality ((laurentUnderCoefficient _).app a)

/-- All native degrees and original scalar times are preserved on genuine supported inputs. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSupportedParameterCoefficientTrack.lean:47"
  "adaptation" "Original supported Spec unit, every track time and actual seed square"]
theorem track_square (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (n : ℕ) (r : unitInterval)
    (x : (prespectrum ((ParameterModels.supported f.left).obj (specUnder.obj a))).space n) :
    (prespectrumMap (laurentModelMap f a)).map n
        (((supportedTrack f.left).homotopy (specUnder.obj a)).level n (r,x)) =
      (((supportedLaurentAction f).track.homotopy a).level n
        (r, (prespectrumMap ((parameterSupportedRowIso f).hom.app a)).map n x)) := by
  have h := model_coefficient_square f a
  exact prespectrumIsoHomotopy_square_apply _ _ _ _ _ _ h
    (onFunctor_whisker_square _ _ _ _ (eqToHom (congrArg (fun k => k.hom.toFunctor) h))
      (supportedUnit f.left (specUnder.obj a)) (supportedLaurentUnit f a)
      (supportedUnit_preserves f a).whisker) n r x

end AlgebraicGeometry.Scheme.Modules.GlobalSupportedParameterCoefficient

