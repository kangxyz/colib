/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalOpenAction
/-! # The original whole fine-to-coarse global seed square -/
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
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

/-- Forgetting support retains the original unit component. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalOpenChangeSeed.lean:25"
  "adaptation" "Original same global unit and whole fine-to-coarse seed square"]
theorem openRowChangeWeak_unit (a : Under R) :
    Preserves ((openRowChangeWeak f).app ((laurentUnderFunctor R).obj a)).hom.toFunctor
      ((globalLaurentAction Q).unit a) ((openLaurentAction f).unit a) := fun _ => rfl

/-- The fine-to-coarse identity preserves every original Laurent-track value. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalOpenChangeSeed.lean:30"
  "adaptation" "Original same global unit and whole fine-to-coarse seed square"]
theorem openRowChangeWeak_track (a : Under R) (n : ℕ) (t : unitInterval)
    (x : (prespectrum ((globalRow Q).obj a)).space n) :
    (prespectrumMap ((openRowChangeWeak f).app ((laurentUnderFunctor R).obj a))).map n
      (((globalLaurentAction Q).track.homotopy a).level n (t, x)) =
    ((openLaurentAction f).track.homotopy a).level n
      (t, (prespectrumMap ((openRowChangeWeak f).app a)).map n x) :=
  LaurentSeed.ModelAction.track_square _ _ _ (openRowChangeWeak_unit f) a n t x

/-- The original global seed commutes with the actual fine-to-coarse identity. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalOpenChangeSeed.lean:39"
  "adaptation" "Original same global unit and whole fine-to-coarse seed square"]
theorem openRowChangeWeak_seed :
    (globalLaurentAction Q).track.seed ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (Functor.whiskerRight (openRowChangeWeak f) prespectrumFunctor) =
    Functor.whiskerRight (openRowChangeWeak f) prespectrumFunctor ≫
      (openLaurentAction f).track.seed :=
  LaurentSeed.Track.seed_square _ _ _ (openRowChangeWeak_track f)

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
