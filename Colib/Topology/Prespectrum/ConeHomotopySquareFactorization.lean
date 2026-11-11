/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.Prespectrum.ConeArrowHomotopy
public import Colib.Topology.Prespectrum.ConeHomotopySquare


/-!
# Literal factorization of the original whole-track cone map

The existing mappingConeSquareMap factors literally into a strict target-change cone map, the
actual arrow-change map carrying the supplied whole homotopy, and a strict source-change cone map.
The middle map has the constructed reverse-track homotopy inverse. The literal factorization
retains the entire original square track; weak equivalence is proved in the downstream owner.
-/
@[expose] public section
noncomputable section

open Topology TopCat
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum

variable {E F E' F' : LoopPrespectrum.{u}}
  (f : E ⟶ F) (g : E' ⟶ F') (a : E ⟶ E') (b : F ⟶ F')
  (H : Homotopy (f ≫ b) (a ≫ g))

/-- The actual cone-square map factors on both its original target and its entire original
cylinder, with the supplied whole square track retained in the middle factor. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ConeHomotopySquareEquivalence.lean:37-57"
  "adaptation" "Original actual-map comparison with the native whole objects retained"]
theorem mappingConeSquareMap_factor :
    mappingConeSquareMap f g a b H =
      mappingConeMap (Arrow.homMk (f := Arrow.mk f) (g := Arrow.mk (f ≫ b))
        (𝟙 E) b (by simp)) ≫
      mappingConeHomotopyMap H ≫
      mappingConeMap (Arrow.homMk (f := Arrow.mk (a ≫ g)) (g := Arrow.mk g)
        a (𝟙 F') (by simp)) := by
  apply mappingCone_hom_ext
  · apply Hom.ext
    funext n
    ext y
    rfl
  · intro n s x
    let m := mappingConeMap (Arrow.homMk (f := Arrow.mk (a ≫ g)) (g := Arrow.mk g)
      a (𝟙 F') (by simp))
    let L := (H.postcomp (mappingConeInclusion g)).levelHomotopy n
    let K := (Homotopy.precomp a (mappingConeHomotopy g)).levelHomotopy n
    let L' := (H.postcomp (mappingConeInclusion (a ≫ g))).levelHomotopy n
    let K' := (mappingConeHomotopy (a ≫ g)).levelHomotopy n
    change (L.trans K) (s, x) = m.map n ((L'.trans K') (s, x))
    have hL := ContinuousMap.HomotopyRel.trans_apply L K (s, x)
    have hR := congrArg (m.map n) (ContinuousMap.HomotopyRel.trans_apply L' K' (s, x))
    refine hL.trans (Eq.trans ?_ hR.symm)
    split_ifs <;> rfl

end Topology.LoopPrespectrum
