/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Homotopy.SquareBoundaryPaths

/-! # Comparison of four prescribed whole boundary paths

Adapted from `Quillen/Waldhausen/Additivity/CompactCoproductNullCoherence.lean:26–52` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original maps, coordinates and path concatenations are retained. -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval

universe u

namespace Topology

/-- The original square interpolation with its four supplied whole boundary paths. -/
def squareEdgeHomotopy {X : Type u} [TopologicalSpace X] {a b c d : X}
    (L : Path a b) (T : Path b d) (B : Path a c) (R : Path c d)
    (F : C(unitInterval × unitInterval, X))
    (hL : ∀ t, F (0, t) = L t) (hT : ∀ t, F (t, 1) = T t)
    (hB : ∀ t, F (t, 0) = B t) (hR : ∀ t, F (1, t) = R t) :
    (L.trans T).Homotopy (B.trans R) := by
  let L' := ((Path.refl (0 : unitInterval)).prod Path.id).map F.continuous
  let T' := (Path.id.prod (Path.refl (1 : unitInterval))).map F.continuous
  let B' := (Path.id.prod (Path.refl (0 : unitInterval))).map F.continuous
  let R' := ((Path.refl (1 : unitInterval)).prod Path.id).map F.continuous
  have ha : a = F (0, 0) := ((hL 0).trans L.source).symm
  have hd : d = F (1, 1) := ((hT 1).trans T.target).symm
  refine ((squareBoundaryPathHomotopy F).pathCast ha hd).cast ?_ ?_
  · apply Path.ext
    funext t
    change (L'.trans T') t = (L.trans T) t
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs
    · exact hL _
    · exact hT _
  · apply Path.ext
    funext t
    change (B'.trans R') t = (B.trans R) t
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs
    · exact hB _
    · exact hR _


end Topology
