/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.Prespectrum.RelativeHomotopy
public import Colib.Topology.Prespectrum.HomotopyLoop

/-! Precomposition of a supplied relative comparison, used for original Bass composition tracks. -/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/RelativeHomotopyWhiskering.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, whole tracks, signs and
    independent parameters are retained. -/
@[expose] public section
open Topology CategoryTheory.Functor
noncomputable section
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum.Homotopy.RelHomotopy
variable {D E F : LoopPrespectrum.{u}} {f g : E ⟶ F} {H K : Homotopy f g}

/-- Precompose every point of the actual two-parameter comparison by the original map. -/
def precomp (h : D ⟶ E) (J : H.RelHomotopy K) :
    (Homotopy.precomp h H).RelHomotopy (Homotopy.precomp h K) where
  level n := {
    toFun z := J.level n (z.1, (z.2.1, h.map n z.2.2))
    continuous_toFun := by fun_prop
    map_zero_left z := (J.level n).apply_zero _
    map_one_left z := (J.level n).apply_one _
    prop' r z hz := by
      apply (J.level n).eq_fst r
      rcases hz with hz | hz | hz
      · exact Or.inl hz
      · exact Or.inr (Or.inl hz)
      · exact Or.inr (Or.inr (hz ▸ h.map_point n)) }
  comm n r s x t :=
    (congrArg (fun y ↦ J.level (n + 1) (r, (s, y)))
      (congrArg (fun p ↦ p t) (h.comm n x))).trans (J.comm n r s (h.map n x) t)

end Topology.LoopPrespectrum.Homotopy.RelHomotopy

namespace Topology.LoopPrespectrum
variable {D E F : LoopPrespectrum.{u}}

/-- Precomposition retains the full original concatenation parametrization. -/
theorem Homotopy.precomp_trans {f g k : E ⟶ F} (h : D ⟶ E)
    (H : Homotopy f g) (K : Homotopy g k) :
    Homotopy.precomp h (H.trans K) = (Homotopy.precomp h H).trans (Homotopy.precomp h K) := by
  apply Homotopy.ext
  funext n
  apply ContinuousMap.ext
  rintro ⟨s, x⟩
  change ((H.levelHomotopy n).trans (K.levelHomotopy n)) (s, h.map n x) =
    ((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n)) (s, x)
  rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split <;> rfl

/-- Postcomposition retains the full original concatenation parametrization. -/
theorem Homotopy.postcomp_trans {f g k : D ⟶ E} (H : Homotopy f g)
    (K : Homotopy g k) (h : E ⟶ F) :
    (H.trans K).postcomp h = (H.postcomp h).trans (K.postcomp h) := by
  apply Homotopy.ext
  funext n
  apply ContinuousMap.ext
  rintro ⟨s, x⟩
  change h.map n (((H.levelHomotopy n).trans (K.levelHomotopy n)) (s, x)) =
    ((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n)) (s, x)
  rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split <;> rfl

/-- Precomposition retains the original reversed path coordinate. -/
theorem Homotopy.precomp_symm {f g : E ⟶ F} (h : D ⟶ E) (H : Homotopy f g) :
    Homotopy.precomp h H.symm = (Homotopy.precomp h H).symm := by
  apply Homotopy.ext
  rfl

/-- Postcomposition retains the original reversed path coordinate. -/
theorem Homotopy.postcomp_symm {f g : D ⟶ E} (H : Homotopy f g) (h : E ⟶ F) :
    H.symm.postcomp h = (H.postcomp h).symm := by
  apply Homotopy.ext
  rfl

end Topology.LoopPrespectrum

-- COL-0324 references
attribute [colib_ref "quillen"
  "Prespectrum/RelativeHomotopyWhiskering.lean:1-80"
  "adaptation" "Actual whole tracks, canonical normalization and operation comparison"]
  Topology.LoopPrespectrum.Homotopy.RelHomotopy.precomp
  Topology.LoopPrespectrum.Homotopy.precomp_trans
  Topology.LoopPrespectrum.Homotopy.postcomp_trans
  Topology.LoopPrespectrum.Homotopy.precomp_symm
  Topology.LoopPrespectrum.Homotopy.postcomp_symm
