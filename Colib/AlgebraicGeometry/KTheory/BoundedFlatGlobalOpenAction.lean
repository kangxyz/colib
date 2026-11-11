/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalOpenModels
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSectionLaurentAction
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryOpenBassSeed
/-! # Original Laurent action on the actual coarse global row -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Topology
open CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open CategoryTheory.Functor.IdentityAutomorphism
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
attribute [local irreducible] boundedAboveFlatGlobalSectionModelFunctor
  boundedAboveFlatCoefficientSectionWaldhausen
  boundedAboveFlatCoefficientOriginalEvaluation
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

/-- Changing weak classes retains the actual original forward global unit. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalOpenAction.lean:28"
  "adaptation" "Original global coarse Laurent action and whole restriction seed square"]
def openLaurentAction : LaurentSeed.ModelAction (openRow f) where
  unit a := globalLaurentUnit Q a
  naturality g := globalLaurentUnit_naturality Q g

/-- Original coarse restriction preserves the entire forward unit component. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalOpenAction.lean:33"
  "adaptation" "Original global coarse Laurent action and whole restriction seed square"]
theorem openRowRestriction_unit (a : Under R) :
    Preserves ((openRowRestriction f).app ((laurentUnderFunctor R).obj a)).hom.toFunctor
      ((openLaurentAction f).unit a)
      ((boundedAboveFlatCoefficientOpenLaurentAction f).unit a) := by
  intro x
  exact rowRestriction_unit Q a x

/-- Every original coarse Laurent-track time commutes with restriction. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalOpenAction.lean:41"
  "adaptation" "Original global coarse Laurent action and whole restriction seed square"]
theorem openRowRestriction_track (a : Under R) (n : ℕ) (t : unitInterval)
    (x : (prespectrum ((openRow f).obj a)).space n) :
    (prespectrumMap ((openRowRestriction f).app ((laurentUnderFunctor R).obj a))).map n
      (((openLaurentAction f).track.homotopy a).level n (t, x)) =
    ((boundedAboveFlatCoefficientOpenLaurentAction f).track.homotopy a).level n
      (t, (prespectrumMap ((openRowRestriction f).app a)).map n x) :=
  LaurentSeed.ModelAction.track_square _ _ _ (openRowRestriction_unit f) a n t x

/-- The actual coarse seed commutes with the original coefficient restriction. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalOpenAction.lean:50"
  "adaptation" "Original global coarse Laurent action and whole restriction seed square"]
theorem openRowRestriction_seed :
    (openLaurentAction f).track.seed ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (Functor.whiskerRight (openRowRestriction f) prespectrumFunctor) =
    Functor.whiskerRight (openRowRestriction f) prespectrumFunctor ≫
      (boundedAboveFlatCoefficientOpenLaurentAction f).track.seed :=
  LaurentSeed.Track.seed_square _ _ _ (openRowRestriction_track f)

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
