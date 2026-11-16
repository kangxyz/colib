/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Covering.HomotopyThinNeighborhoods
public import Colib.Topology.DoubleMappingCylinder.Collars
public import Colib.Topology.Pushout.CompactParameter
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Tactic.NormNum

/-! # Actual double-cylinder thin neighborhoods from its two open collars

LPC comes from the original pushout sum quotient. The two
ambient-thin structures on its ends transfer through their actual collar SDRs.
No injectivity of either attachment and no local-topology transfer by HE is used.


Adapted from `Quillen/Topology/DoubleMappingCylinder/ThinNeighborhoods.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section

open Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Set
open scoped Topology unitInterval
universe u
namespace TopCat.DoubleCylinder

variable {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
  {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
  (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)

include sq in
/-- The literal double-cylinder pushout is LPC when its three original spaces are LPC. -/
theorem locallyPathConnectedSpace [LocallyPathConnectedSpace A]
    [LocallyPathConnectedSpace B] [LocallyPathConnectedSpace C] :
    LocallyPathConnectedSpace D := by
  let : LocallyPathConnectedSpace unitInterval :=
    (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  let : LocallyPathConnectedSpace (ULift.{u} unitInterval) :=
    Homeomorph.ulift.symm.locallyPathConnectedSpace
  let : LocallyPathConnectedSpace (↑(A ⊗ TopCat.I) ⊕ ↑(TopCat.of (B ⊕ C))) := by
    change LocallyPathConnectedSpace ((A × ULift.{u} unitInterval) ⊕ (B ⊕ C))
    infer_instance
  exact (Topology.pushout_sum_isQuotientMap sq).locallyPathConnectedSpace

/-- The left collar supplies an open ambient-thin neighborhood of each of its points. -/
theorem leftCollar_exists_open_ambientPathThin (EB : PathThinNeighborhoods B)
    (cut : unitInterval) (hcut : 0 < cut) (d : LeftCollar f g sq cut) :
    ∃ V : Set D, IsOpen V ∧ d.val ∈ V ∧ AmbientPathThin V := by
  let R := leftCollarStrongDeformationRetract f g sq cut hcut
  let j : C(LeftCollar f g sq cut, D) := ⟨Subtype.val, continuous_subtype_val⟩
  let i : C(B, D) := j.comp (leftCollarInclusion f g sq cut hcut).hom
  let H : (i.comp R.r.hom).Homotopy j :=
    (ContinuousMap.Homotopy.refl j).comp (homotopyOfCylinder R.H R.H₀ R.H₁)
  exact exists_open_ambientPathThin_of_homotopy (leftCollar_isOpen f g sq cut)
    R.r.hom i H EB d

/-- The right collar supplies an open ambient-thin neighborhood of each of its points. -/
theorem rightCollar_exists_open_ambientPathThin (EC : PathThinNeighborhoods C)
    (cut : unitInterval) (hcut : cut < 1) (d : RightCollar f g sq cut) :
    ∃ V : Set D, IsOpen V ∧ d.val ∈ V ∧ AmbientPathThin V := by
  let R := rightCollarStrongDeformationRetract f g sq cut hcut
  let j : C(RightCollar f g sq cut, D) := ⟨Subtype.val, continuous_subtype_val⟩
  let i : C(C, D) := j.comp (rightCollarInclusion f g sq cut hcut).hom
  let H : (i.comp R.r.hom).Homotopy j :=
    (ContinuousMap.Homotopy.refl j).comp (homotopyOfCylinder R.H R.H₀ R.H₁)
  exact exists_open_ambientPathThin_of_homotopy (rightCollar_isOpen f g sq cut)
    R.r.hom i H EC d

include sq in
/-- The two genuinely overlapping collars cover every point of the original pushout. -/
theorem exists_open_ambientPathThin (EB : PathThinNeighborhoods B)
    (EC : PathThinNeighborhoods C) (d : D) :
    ∃ V : Set D, IsOpen V ∧ d ∈ V ∧ AmbientPathThin V := by
  let leftCut : unitInterval := ⟨2 / 3, by norm_num⟩
  let rightCut : unitInterval := ⟨1 / 3, by norm_num⟩
  have hL : 0 < leftCut := by change (0 : ℝ) < 2 / 3; norm_num
  have hR : rightCut < 1 := by change (1 / 3 : ℝ) < 1; norm_num
  have hcuts : rightCut < leftCut := by change (1 / 3 : ℝ) < 2 / 3; norm_num
  have hd : d ∈ leftCollarSet f g sq leftCut ∪ rightCollarSet f g sq rightCut := by
    rw [collar_cover f g sq leftCut rightCut hcuts]
    exact mem_univ d
  rcases hd with hd | hd
  · exact leftCollar_exists_open_ambientPathThin f g sq EB leftCut hL ⟨d, hd⟩
  · exact rightCollar_exists_open_ambientPathThin f g sq EC rightCut hR ⟨d, hd⟩

/-- Actual LPC and the two collar homotopies construct the full thin-neighborhood structure. -/
def pathThinNeighborhoods [LocallyPathConnectedSpace A]
    [LocallyPathConnectedSpace B] [LocallyPathConnectedSpace C]
    (EB : PathThinNeighborhoods B) (EC : PathThinNeighborhoods C) :
    PathThinNeighborhoods D := by
  let := locallyPathConnectedSpace f g sq
  exact PathThinNeighborhoods.ofOpenAmbientThin (exists_open_ambientPathThin f g sq EB EC)

end TopCat.DoubleCylinder
