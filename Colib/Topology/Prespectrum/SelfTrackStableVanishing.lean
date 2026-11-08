/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.Topology.Prespectrum.SelfTrackStableNullEvaluation

/-!
# Direct stable vanishing of the original null-conjugated self-track

Vanishing of the original intermediate stable group in degree one higher
annihilates the actual self-track operation and hence the original supplied-null
map in every integer degree. The argument uses its proved original factorization,
without a levelwise vanishing condition or an Omega replacement.
-/
/-! Implementation provenance:
`Quillen/Topology/Prespectrum/SelfTrackStableVanishing.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The native objects, complete tracks, original coordinates and signs are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u
namespace Topology.LoopPrespectrum
variable {E F G : LoopPrespectrum.{u}} {f : E ⟶ F}

/-- A trivial original one-higher stable target annihilates the actual stable operation. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackStableVanishing.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.stableOperation_eq_zero_of_subsingleton (H : Homotopy f f) (d : ℤ)
    (hF : Subsingleton (stableHomotopyGroup F (d + 1))) : H.stableOperation d = 0 := by
  let := hF
  apply AddCommGrpCat.ext
  intro a
  exact Subsingleton.elim _ _

/-- The exact original supplied-null map vanishes from its original stable obstruction alone. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackStableVanishing.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.nullLoopMap_stableMap_zero_of_stable (H : Homotopy f f) (j : F ⟶ G)
    (N : Homotopy (f ≫ j) (zeroHom E G)) (d : ℤ)
    (hF : Subsingleton (stableHomotopyGroup F (d + 1))) :
    (stableHomotopyFunctor d).map ((H.postcomp j).nullLoopMap N) = 0 := by
  apply (cancel_mono (parameterStableHomotopyIso G d).hom).mp
  rw [H.nullLoopMap_stableHomotopy_postcomp j N d,
    H.stableOperation_eq_zero_of_subsingleton d hF]
  simp only [zero_comp]

/-- The unchanged original mapping-cone transition satisfies the same all-integer criterion. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackStableVanishing.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem mappingConeLoopTransition_stableMap_zero_of_stable (f : E ⟶ F)
    (H : Homotopy f f) (d : ℤ) (hF : Subsingleton (stableHomotopyGroup F (d + 1))) :
    (stableHomotopyFunctor d).map (mappingConeLoopTransition f H) = 0 :=
  H.nullLoopMap_stableMap_zero_of_stable (mappingConeInclusion f) (mappingConeHomotopy f) d hF

end Topology.LoopPrespectrum

attribute [colib_tag "COL-0321"]
  Topology.LoopPrespectrum.Homotopy.nullLoopMap_stableMap_zero_of_stable
