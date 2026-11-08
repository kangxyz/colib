/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.KTheory.Waldhausen.Iterated.ExactCompositionHomotopy
public import Colib.Topology.Prespectrum.SelfTrackRelativeHomotopy
public import Colib.Topology.Prespectrum.SelfTrackStableConcatenation

/-! # Stable operations of actual canonically rebased exact-functor automorphisms -/
/-! Implementation provenance:
`Quillen/Waldhausen/SConstruction/Iterated/ExactSelfTrackStableOperation.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The native objects, complete tracks, original coordinates and signs are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology.LoopPrespectrum
universe u v
namespace CategoryTheory.Waldhausen.IteratedS
open SmallWaldhausenCategory Topology SSet
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (W : Structure C) (V : Structure D) {F : C ⥤ D}
variable (hF : IsExact W.cof W.weq V.cof V.weq F)

/-- The original composition triangle gives the actual reversed sum on all stable groups. -/
@[colib_ref "quillen"
    "Waldhausen/SConstruction/Iterated/ExactSelfTrackStableOperation.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem exactIsoSelfTrack_stableOperation_comp (e e' : F ≅ F) (d : ℤ) :
    (exactOriginalPrespectrumIsoHomotopy W V hF hF (e ≪≫ e')).stableOperation d =
      (exactOriginalPrespectrumIsoHomotopy W V hF hF e').stableOperation d +
        (exactOriginalPrespectrumIsoHomotopy W V hF hF e).stableOperation d :=
  ((exactOriginalPrespectrumIsoCompositionHomotopy W V hF hF hF e e').stableOperation_eq d).trans
    (Homotopy.stableOperation_trans _ _ d)

/-- Idempotence of the original identity composition triangle forces its operation to zero. -/
@[colib_ref "quillen"
    "Waldhausen/SConstruction/Iterated/ExactSelfTrackStableOperation.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem exactIsoSelfTrack_stableOperation_refl (d : ℤ) :
    (exactOriginalPrespectrumIsoHomotopy W V hF hF (Iso.refl F)).stableOperation d = 0 := by
  have h := exactIsoSelfTrack_stableOperation_comp W V hF (Iso.refl F) (Iso.refl F) d
  simp only [Iso.refl_trans] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

/-- The actual inverse natural isomorphism gives the negative original stable operation. -/
@[colib_ref "quillen"
    "Waldhausen/SConstruction/Iterated/ExactSelfTrackStableOperation.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem exactIsoSelfTrack_stableOperation_symm (e : F ≅ F) (d : ℤ) :
    (exactOriginalPrespectrumIsoHomotopy W V hF hF e.symm).stableOperation d =
      -(exactOriginalPrespectrumIsoHomotopy W V hF hF e).stableOperation d := by
  have h := exactIsoSelfTrack_stableOperation_comp W V hF e e.symm d
  rw [Iso.self_symm_id, exactIsoSelfTrack_stableOperation_refl] at h
  exact eq_neg_of_add_eq_zero_left h.symm

end CategoryTheory.Waldhausen.IteratedS
