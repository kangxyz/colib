/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.RelativeHomotopyConjugation
public import Colib.Topology.Prespectrum.RelativeHomotopyLevels

/-!
# Pointwise postcomposition of the original relative path operations

These lemmas preserve a supplied pointwise image identity through the actual relative
concatenations and reparameterizations. They compare existing families at the same source
point and independent coordinates; they do not construct a missing comparison or filler.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum

/-- The same original point and path time give a prescribed image in a second target. -/
def Homotopy.MappedAt {E F G : LoopPrespectrum.{u}}
    {f g : E ⟶ F} {f' g' : E ⟶ G} (H : Homotopy f g)
    (j : F ⟶ G) (n : ℕ) (x : E.space n) (H' : Homotopy f' g') : Prop :=
  ∀ s, j.map n (H.level n (s, x)) = H'.level n (s, x)

/-- Both original independent times give a prescribed image of the whole relative family. -/
def Homotopy.RelHomotopy.MappedAt {E F G : LoopPrespectrum.{u}}
    {f g : E ⟶ F} {f' g' : E ⟶ G}
    {H K : Homotopy f g} {H' K' : Homotopy f' g'}
    (J : H.RelHomotopy K) (j : F ⟶ G) (n : ℕ) (x : E.space n)
    (J' : H'.RelHomotopy K') : Prop :=
  ∀ r s, j.map n (J.level n (r, (s, x))) = J'.level n (r, (s, x))

namespace Homotopy.MappedAt
variable {E F G : LoopPrespectrum.{u}} {j : F ⟶ G} {n : ℕ} {x : E.space n}
  {f g h : E ⟶ F} {f' g' h' : E ⟶ G}
  {H : Homotopy f g} {H' : Homotopy f' g'}

/-- Concatenation keeps both actual half-intervals under the given target map. -/
theorem trans {K : Homotopy g h} {K' : Homotopy g' h'}
    (hH : H.MappedAt j n x H') (hK : K.MappedAt j n x K') :
    (H.trans K).MappedAt j n x (H'.trans K') := by
  intro s
  change j.map n (((H.levelHomotopy n).trans (K.levelHomotopy n)) (s, x)) =
    ((H'.levelHomotopy n).trans (K'.levelHomotopy n)) (s, x)
  rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split
  · exact hH _
  · exact hK _

/-- Path reversal uses the same reversed coordinate on both sides. -/
theorem symm (hH : H.MappedAt j n x H') : H.symm.MappedAt j n x H'.symm := by
  intro s
  exact hH (unitInterval.symm s)

/-- The constant relative comparison retains the supplied whole path identity. -/
theorem refl (hH : H.MappedAt j n x H') :
    (Homotopy.RelHomotopy.refl H).MappedAt j n x (Homotopy.RelHomotopy.refl H') := by
  intro _ s
  exact hH s

end Homotopy.MappedAt
namespace Homotopy.RelHomotopy.MappedAt
variable {E F G : LoopPrespectrum.{u}} {j : F ⟶ G} {n : ℕ} {x : E.space n}
  {f g h : E ⟶ F} {f' g' h' : E ⟶ G}
  {H K L : Homotopy f g} {H' K' L' : Homotopy f' g'}
  {J : H.RelHomotopy K} {J' : H'.RelHomotopy K'}

/-- Comparison reversal changes only the same comparison coordinate. -/
theorem symm (hJ : J.MappedAt j n x J') : J.symm.MappedAt j n x J'.symm := by
  intro r s
  exact hJ (unitInterval.symm r) s

/-- Original path reversal leaves the comparison coordinate independent. -/
theorem symmPath (hJ : J.MappedAt j n x J') :
    J.symmPath.MappedAt j n x J'.symmPath := by
  intro r s
  exact hJ r (unitInterval.symm s)

/-- Relative concatenation preserves its actual comparison-time subdivision. -/
theorem trans {N : K.RelHomotopy L} {N' : K'.RelHomotopy L'}
    (hJ : J.MappedAt j n x J') (hN : N.MappedAt j n x N') :
    (J.trans N).MappedAt j n x (J'.trans N') := by
  intro r s
  change j.map n (((J.level n).trans (N.level n)) (r, (s, x))) =
    ((J'.level n).trans (N'.level n)) (r, (s, x))
  rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split
  · exact hJ _ s
  · exact hN _ s

private theorem hcomp_apply {D T : LoopPrespectrum.{u}} {a b c : D ⟶ T}
    {A A' : Homotopy a b} {B B' : Homotopy b c}
    (M : A.RelHomotopy A') (N : B.RelHomotopy B') (k : ℕ) (r s : unitInterval)
    (y : D.space k) :
    (M.hcomp N).level k (r, (s, y)) =
      if hs : (s : ℝ) ≤ 1 / 2 then
        M.level k (r,
          (⟨2 * s, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩, y))
      else N.level k (r, (⟨2 * s - 1,
        unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hs).le, s.2.2⟩⟩, y)) :=
  ContinuousMap.Homotopy.trans_apply _ _ _

/-- Horizontal concatenation keeps its original path-time halves under postcomposition. -/
theorem hcomp {A B : Homotopy g h} {A' B' : Homotopy g' h'}
    {N : A.RelHomotopy B} {N' : A'.RelHomotopy B'}
    (hJ : J.MappedAt j n x J') (hN : N.MappedAt j n x N') :
    (J.hcomp N).MappedAt j n x (J'.hcomp N') := by
  intro r s
  rw [hcomp_apply, hcomp_apply]
  split
  · exact hJ r _
  · exact hN r _

/-- Proposition-level changes of the two boundary tracks leave every comparison value intact. -/
theorem transport {D T T' : LoopPrespectrum.{u}}
    {a b : D ⟶ T} {a' b' : D ⟶ T'}
    {A B C D' : Homotopy a b} {A' B' C' D'' : Homotopy a' b'}
    (eA : A = B) (eC : C = D') (eA' : A' = B') (eC' : C' = D'')
    (p : A.RelHomotopy C = B.RelHomotopy D')
    (q : A'.RelHomotopy C' = B'.RelHomotopy D'')
    (M : A.RelHomotopy C) (M' : A'.RelHomotopy C')
    (map : T ⟶ T') (k : ℕ) (y : D.space k) (hM : M.MappedAt map k y M') :
    (p.mp M).MappedAt map k y (q.mp M') := by
  subst B
  subst D'
  subst B'
  subst D''
  exact hM

end Homotopy.RelHomotopy.MappedAt
end Topology.LoopPrespectrum
