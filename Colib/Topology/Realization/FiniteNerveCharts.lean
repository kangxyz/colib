/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.OrderedCoverNerve
public import Colib.Topology.Realization.NumerableConnectorCover
public import Colib.Topology.Realization.DescAcross
public import Mathlib.Data.Finset.Sort

/-!
# Actual finite charts of an ordered cover nerve

These charts use the increasing enumeration of a finite common-intersection
set. Inclusion compatibility is an equality of original realization charts,
not an assumed coordinate reconstruction or a metric-to-weak inverse.
-/

open SSet Topology CategoryTheory

/-! Implementation source: `Quillen/Topology/Realization/FiniteNerveCharts.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps and proofs are retained. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Convexity CategoryTheory Opposite
open scoped Topology Simplicial
universe u v
namespace Topology.NumerableConnectorCover
variable {A : Type u} {ι : Type v} [LinearOrder ι]

/-- The dimension of a nonempty finite vertex set. -/
def finiteFaceDim (s : Finset ι) : ℕ := s.card - 1

omit [LinearOrder ι] in
/-- A nonempty finite vertex set has exactly one more vertex than its dimension. -/
theorem finiteFace_card (s : Finset ι) (hs : s.Nonempty) : s.card = finiteFaceDim s + 1 := by
  have h := Finset.card_pos.mpr hs
  dsimp [finiteFaceDim]
  omega

/-- Inclusion of finite vertex sets, retaining each actual index. -/
def finiteFaceInclusion {s t : Finset ι} (h : s ⊆ t) : s →o t where
  toFun i := ⟨i.1, h i.2⟩
  monotone' _ _ hij := hij

/-- A finite common-intersection set gives an actual increasing simplex. -/
def finiteFaceSimplex (W : ι → Set A) (s : Finset ι) (hs : s.Nonempty)
    (hface : IsNerveFace W s) : (orderedNerve W).toSSet.obj (op ⦋finiteFaceDim s⦌) :=
  ⟨(s.orderEmbOfFin (finiteFace_card s hs)).monotone.functor, by
    obtain ⟨x, hx⟩ := hface
    exact ⟨x, fun j ↦ hx _ (s.orderEmbOfFin_mem _ j)⟩⟩

/-- Finite barycentric weights are sent to the corresponding original realized simplex. -/
def finiteNerveChart (W : ι → Set A) (s : Finset ι) (hs : s.Nonempty)
    (hface : IsNerveFace W s) : C(StdSimplex ℝ s, |(orderedNerve W).toSSet|) :=
  (realizationSimplex (finiteFaceSimplex W s hs hface)).comp
    ⟨StdSimplex.map (s.orderIsoOfFin (finiteFace_card s hs)).symm,
      StdSimplex.continuous_map ℝ _⟩

/-- The actual increasing simplex operator induced by a finite-set inclusion. -/
def finiteFaceOperator {s t : Finset ι} (hs : s.Nonempty) (ht : t.Nonempty) (hst : s ⊆ t) :
    ⦋finiteFaceDim s⦌ ⟶ ⦋finiteFaceDim t⦌ :=
  SimplexCategory.Hom.mk {
    toFun i := (t.orderIsoOfFin (finiteFace_card t ht)).symm
      (finiteFaceInclusion hst (s.orderIsoOfFin (finiteFace_card s hs) i))
    monotone' _ _ hij := (t.orderIsoOfFin (finiteFace_card t ht)).symm.monotone
      ((s.orderIsoOfFin (finiteFace_card s hs)).monotone hij) }

/-- The simplex operator restricts the larger actual vertex list to the smaller one. -/
theorem finiteFaceSimplex_map (W : ι → Set A) {s t : Finset ι}
    (hs : s.Nonempty) (ht : t.Nonempty) (hst : s ⊆ t)
    (hsface : IsNerveFace W s) (htface : IsNerveFace W t) :
    (orderedNerve W).toSSet.map (finiteFaceOperator hs ht hst).op
      (finiteFaceSimplex W t ht htface) = finiteFaceSimplex W s hs hsface := by
  apply Subtype.ext
  ext i
  change (t.orderEmbOfFin (finiteFace_card t ht))
    ((t.orderIsoOfFin (finiteFace_card t ht)).symm
      (finiteFaceInclusion hst (s.orderIsoOfFin (finiteFace_card s hs) i))) =
        s.orderEmbOfFin (finiteFace_card s hs) i
  change ((t.orderIsoOfFin (finiteFace_card t ht))
    ((t.orderIsoOfFin (finiteFace_card t ht)).symm
      (finiteFaceInclusion hst (s.orderIsoOfFin (finiteFace_card s hs) i)))).1 = _
  rw [OrderIso.apply_symm_apply]
  rfl

/-- The two ways to transport a smaller weight vector into larger ordered coordinates agree. -/
theorem finiteFace_weights_naturality {s t : Finset ι}
    (hs : s.Nonempty) (ht : t.Nonempty) (hst : s ⊆ t) (x : StdSimplex ℝ s) :
    (x.map (s.orderIsoOfFin (finiteFace_card s hs)).symm).map
      (finiteFaceOperator hs ht hst).toOrderHom =
    (x.map (finiteFaceInclusion hst)).map (t.orderIsoOfFin (finiteFace_card t ht)).symm := by
  rw [StdSimplex.map_map, StdSimplex.map_map]
  congr 1
  funext i
  change (t.orderIsoOfFin (finiteFace_card t ht)).symm
    (finiteFaceInclusion hst ((s.orderIsoOfFin (finiteFace_card s hs))
      ((s.orderIsoOfFin (finiteFace_card s hs)).symm i))) =
    (t.orderIsoOfFin (finiteFace_card t ht)).symm (finiteFaceInclusion hst i)
  rw [OrderIso.apply_symm_apply]

/-- Exact chart compatibility under zero-coordinate insertion, in the original weak realization. -/
theorem finiteNerveChart_inclusion (W : ι → Set A) {s t : Finset ι}
    (hs : s.Nonempty) (ht : t.Nonempty) (hst : s ⊆ t)
    (hsface : IsNerveFace W s) (htface : IsNerveFace W t) (x : StdSimplex ℝ s) :
    finiteNerveChart W t ht htface (x.map (finiteFaceInclusion hst)) =
      finiteNerveChart W s hs hsface x := by
  change realizationSimplex (finiteFaceSimplex W t ht htface)
      ((x.map (finiteFaceInclusion hst)).map (t.orderIsoOfFin (finiteFace_card t ht)).symm) = _
  rw [← finiteFace_weights_naturality hs ht hst x]
  change realizationSimplex (finiteFaceSimplex W t ht htface)
    (StdSimplex.map (finiteFaceOperator hs ht hst)
      (x.map (s.orderIsoOfFin (finiteFace_card s hs)).symm)) = _
  rw [realizationSimplex_naturality, finiteFaceSimplex_map W hs ht hst hsface htface]
  rfl

variable [TopologicalSpace A]

omit [LinearOrder ι] in
/-- Sum one makes the original positive partition support nonempty. -/
theorem partition_finsupport_nonempty (ρ : PartitionOfUnity ι A) (x : A) :
    (ρ.finsupport x).Nonempty := by
  by_contra h
  have he : ρ.finsupport x = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  have ht := ρ.sum_finsupport (Set.mem_univ x)
  simp only [he, Finset.sum_empty, zero_ne_one] at ht

/-- Finite chart coordinates are unchanged by enlarging their supporting vertex set. -/
theorem finiteChart_map_inclusion (ρ : PartitionOfUnity ι A) {s t : Finset ι}
    (hst : s ⊆ t) (x : chartDomain ρ s) :
    (finiteChart ρ s x).map (finiteFaceInclusion hst) =
      finiteChart ρ t ⟨x.1, x.2.trans hst⟩ := by
  apply StdSimplex.ext
  ext j
  have hi : Function.Injective (finiteFaceInclusion hst) := by
    intro a b h
    exact Subtype.ext (congrArg (fun j : t ↦ j.1) h)
  by_cases hj : j.1 ∈ s
  · let i : s := ⟨j.1, hj⟩
    have he : finiteFaceInclusion hst i = j := Subtype.ext rfl
    rw [StdSimplex.weights_map, ← he, Finsupp.mapDomain_apply_of_injective hi]
    rfl
  · have hn : j ∉ Set.range (finiteFaceInclusion hst) := by
      rintro ⟨i, hi⟩
      apply hj
      rw [← congrArg (fun j : t ↦ j.1) hi]
      exact i.2
    rw [StdSimplex.weights_map, Finsupp.mapDomain_of_notMem_range _ _ hn]
    symm
    change ρ j.1 x.1 = 0
    by_contra hne
    exact hj (x.2 ((ρ.mem_finsupport x.1).mpr hne))

end Topology.NumerableConnectorCover
