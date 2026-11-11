/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalOpenAction
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalFullOpenModels

/-! # Actual global open restriction preserves the original global seed -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open KTheory.Bass CategoryTheory.Functor.IdentityAutomorphism
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

omit [IsOpenImmersion f.left] in
private theorem scalar_open (a : Under R) (r : (Γ(Spec a.right, ⊤))ˣ) :
    Units.map (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
      (show (op Q, a) ⟶ (op P, a) from (f.op, 𝟙 a))).appTop.hom.toMonoidHom
      (boundedAboveFlatCoefficientUnit (op Q, a) r) =
      boundedAboveFlatCoefficientUnit (op P, a) r := by
  rw [boundedAboveFlatCoefficientUnit_map]
  simp

/-- Actual open reindexing retains the original Laurent coordinate. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalFullOpenSeed.lean:36"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
theorem globalOpenRestriction_unit (a : Under R) :
    Preserves ((globalOpenRestriction f).app ((laurentUnderFunctor R).obj a)).hom.toFunctor
      ((openLaurentAction f).unit a) ((globalLaurentAction P).unit a) := by
  exact boundedAboveFlatGlobalSectionUnit_reindex_of_eq
    ((AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).map
      (show (op Q, (laurentUnderFunctor R).obj a) ⟶
          (op P, (laurentUnderFunctor R).obj a) from (f.op, 𝟙 _)))
    _ _ (scalar_open f _ _)

/-- Actual open reindexing preserves every original Laurent-track value. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalFullOpenSeed.lean:46"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
theorem globalOpenRestriction_track (a : Under R) (n : ℕ) (t : unitInterval)
    (x : (prespectrum ((openRow f).obj a)).space n) :
    (prespectrumMap ((globalOpenRestriction f).app ((laurentUnderFunctor R).obj a))).map n
      (((openLaurentAction f).track.homotopy a).level n (t, x)) =
    ((globalLaurentAction P).track.homotopy a).level n
      (t, (prespectrumMap ((globalOpenRestriction f).app a)).map n x) :=
  LaurentSeed.ModelAction.track_square _ _ _ (globalOpenRestriction_unit f) a n t x

/-- The original global seed commutes with actual open restriction. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalFullOpenSeed.lean:55"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
theorem globalOpenRestriction_seed :
    (openLaurentAction f).track.seed ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (Functor.whiskerRight (globalOpenRestriction f) prespectrumFunctor) =
    Functor.whiskerRight (globalOpenRestriction f) prespectrumFunctor ≫
      (globalLaurentAction P).track.seed :=
  LaurentSeed.Track.seed_square _ _ _ (globalOpenRestriction_track f)

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex

