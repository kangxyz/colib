/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.Prespectrum.RelativeHomotopy
public import Colib.Topology.Prespectrum.HomotopyLoop

/-! Transport relative comparisons along equality of their actual continuous levels. -/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/RelativeHomotopyLevels.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, whole tracks, signs and
    independent parameters are retained. -/
@[expose] public section
open Topology CategoryTheory.Functor
noncomputable section
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum.Homotopy.RelHomotopy

/-- Preserve every original comparison coordinate while identifying the two specified tracks. -/
def ofLevels {E F : LoopPrespectrum.{u}}
    {f g f' g' : E ⟶ F} {H K : Homotopy f g}
    (J : H.RelHomotopy K) (H' K' : Homotopy f' g')
    (hH : ∀ n, H'.level n = H.level n) (hK : ∀ n, K'.level n = K.level n) :
    H'.RelHomotopy K' where
  level n := {
    toFun := J.level n
    continuous_toFun := (J.level n).continuous
    map_zero_left z := by simpa only [hH n] using (J.level n).apply_zero z
    map_one_left z := by simpa only [hK n] using (J.level n).apply_one z
    prop' r z hz := by
      change J.level n (r, z) = H'.level n z
      rw [hH n]
      exact (J.level n).eq_fst r hz }
  comm n r s x t := J.comm n r s x t

end Topology.LoopPrespectrum.Homotopy.RelHomotopy

namespace Topology.LoopPrespectrum
/-- Concatenation preserves literal whole-level identities, independently of endpoint transports. -/
theorem Homotopy.trans_level_congr {E F : LoopPrespectrum.{u}}
    {a b c a' b' c' : E ⟶ F} (H : Homotopy a b) (K : Homotopy b c)
    (H' : Homotopy a' b') (K' : Homotopy b' c') (n : ℕ)
    (hH : H.level n = H'.level n) (hK : K.level n = K'.level n) :
    (H.trans K).level n = (H'.trans K').level n := by
  apply ContinuousMap.ext
  rintro ⟨s, x⟩
  change ((H.levelHomotopy n).trans (K.levelHomotopy n)) (s, x) =
    ((H'.levelHomotopy n).trans (K'.levelHomotopy n)) (s, x)
  rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split
  · exact DFunLike.congr_fun hH _
  · exact DFunLike.congr_fun hK _

/-- Precomposition preserves full-level equality, regardless of endpoint transports. -/
theorem Homotopy.precomp_level_congr {D E F : LoopPrespectrum.{u}}
    {a b a' b' : E ⟶ F} (h : D ⟶ E) (H : Homotopy a b) (H' : Homotopy a' b')
    (n : ℕ) (he : H.level n = H'.level n) :
    (Homotopy.precomp h H).level n = (Homotopy.precomp h H').level n := by
  apply ContinuousMap.ext
  intro z
  exact DFunLike.congr_fun he (z.1, h.map n z.2)

/-- Postcomposition preserves full-level equality, regardless of endpoint transports. -/
theorem Homotopy.postcomp_level_congr {D E F : LoopPrespectrum.{u}}
    {a b a' b' : D ⟶ E} (H : Homotopy a b) (H' : Homotopy a' b') (h : E ⟶ F)
    (n : ℕ) (he : H.level n = H'.level n) :
    (H.postcomp h).level n = (H'.postcomp h).level n := by
  apply ContinuousMap.ext
  intro z
  exact congrArg (h.map n) (DFunLike.congr_fun he z)

/-- Reversal preserves the original full-level equality, independently of endpoint transports. -/
theorem Homotopy.symm_level_congr {E F : LoopPrespectrum.{u}}
    {a b a' b' : E ⟶ F} (H : Homotopy a b) (H' : Homotopy a' b')
    (n : ℕ) (he : H.level n = H'.level n) : H.symm.level n = H'.symm.level n := by
  apply ContinuousMap.ext
  rintro ⟨s, x⟩
  exact DFunLike.congr_fun he (unitInterval.symm s, x)

end Topology.LoopPrespectrum

-- COL-0324 references
attribute [colib_ref "quillen"
  "Prespectrum/RelativeHomotopyLevels.lean:1-79"
  "adaptation" "Actual whole tracks, canonical normalization and operation comparison"]
  Topology.LoopPrespectrum.Homotopy.RelHomotopy.ofLevels
  Topology.LoopPrespectrum.Homotopy.trans_level_congr
  Topology.LoopPrespectrum.Homotopy.precomp_level_congr
  Topology.LoopPrespectrum.Homotopy.postcomp_level_congr
  Topology.LoopPrespectrum.Homotopy.symm_level_congr
