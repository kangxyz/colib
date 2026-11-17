/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Covering.LocalConnectorHypotheses

/-! # Ambient path thinness transported by actual local homotopies

Endpoint tracks need not be constant. Their classes are
retained and cancelled; the homotopy need not preserve the target thin set.


Adapted from `Quillen/Topology/Covering/HomotopyThinNeighborhoods.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
open Set Topology
open scoped unitInterval
universe u v w
namespace Topology

variable {Z : Type w} {X : Type u} {Y : Type v}
  [TopologicalSpace Z] [TopologicalSpace X] [TopologicalSpace Y]

/-- An actual map homotopy transfers equality of two path classes with common endpoints. -/
theorem path_map_homotopic_of_homotopy {F G : C(Z, X)} (H : F.Homotopy G)
    {a b : Z} (p q : Path a b)
    (h : (p.map F.continuous).Homotopic (q.map F.continuous)) :
    (p.map G.continuous).Homotopic (q.map G.continuous) := by
  have hp := Path.Homotopic.Quotient.eq.mpr (Path.Homotopic.map_trans_evalAt H p)
  have hq := Path.Homotopic.Quotient.eq.mpr (Path.Homotopic.map_trans_evalAt H q)
  simp only [Path.Homotopic.Quotient.mk_trans] at hp hq
  have hh := congrArg (fun r => r.trans (Path.Homotopic.Quotient.mk (H.evalAt b)))
    (Path.Homotopic.Quotient.eq.mpr h)
  have heq := hp.symm.trans (hh.trans hq)
  have hc := congrArg (fun r => (Path.Homotopic.Quotient.mk (H.evalAt a)).symm.trans r) heq
  apply Path.Homotopic.Quotient.eq.mp
  simpa only [← Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans] using hc

/-- A thin target set pulls back to ambient thinness through a local homotopy factorization. -/
theorem ambientPathThin_image_preimage_of_homotopy {U : Set X}
    (r : C(U, Y)) (i : C(Y, X))
    (H : (i.comp r).Homotopy (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)))
    {V : Set Y} (hV : AmbientPathThin V) :
    AmbientPathThin (Subtype.val '' (r ⁻¹' V)) := by
  intro x y p q hp hq
  have hsub : Subtype.val '' (r ⁻¹' V) ⊆ U := by
    rintro z ⟨z', _, rfl⟩
    exact z'.property
  let x' : U := ⟨x, hsub (by simpa using hp 0)⟩
  let y' : U := ⟨y, hsub (by simpa using hp 1)⟩
  let p' : Path x' y' :=
    { toFun t := ⟨p t, hsub (hp t)⟩
      continuous_toFun := p.continuous.subtype_mk _
      source' := Subtype.ext p.source
      target' := Subtype.ext p.target }
  let q' : Path x' y' :=
    { toFun t := ⟨q t, hsub (hq t)⟩
      continuous_toFun := q.continuous.subtype_mk _
      source' := Subtype.ext q.source
      target' := Subtype.ext q.target }
  have hpr : ∀ t, r (p' t) ∈ V := by
    intro t
    obtain ⟨z, hz, he⟩ := hp t
    have he' : p' t = z := Subtype.ext he.symm
    change r z ∈ V at hz
    simpa only [he'] using hz
  have hqr : ∀ t, r (q' t) ∈ V := by
    intro t
    obtain ⟨z, hz, he⟩ := hq t
    have he' : q' t = z := Subtype.ext he.symm
    change r z ∈ V at hz
    simpa only [he'] using hz
  have hm := (hV (p'.map r.continuous) (q'.map r.continuous) hpr hqr).map i
  have hm' : (p'.map (i.comp r).continuous).Homotopic
      (q'.map (i.comp r).continuous) := hm
  have hlast := path_map_homotopic_of_homotopy H p' q' hm'
  have hpmap : p'.map continuous_subtype_val = p := by ext t; rfl
  have hqmap : q'.map continuous_subtype_val = q := by ext t; rfl
  change (p'.map continuous_subtype_val).Homotopic (q'.map continuous_subtype_val) at hlast
  simpa only [hpmap, hqmap] using hlast

/-- Each point of an open local retraction chart has an open ambient-thin neighborhood. -/
theorem exists_open_ambientPathThin_of_homotopy {U : Set X} (hU : IsOpen U)
    (r : C(U, Y)) (i : C(Y, X))
    (H : (i.comp r).Homotopy (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)))
    (A : PathThinNeighborhoods Y) (x : U) :
    ∃ V : Set X, IsOpen V ∧ x.val ∈ V ∧ AmbientPathThin V := by
  refine ⟨Subtype.val '' (r ⁻¹' A.neighborhood (r x)),
    hU.isOpenMap_subtype_val _ ((A.isOpen_neighborhood (r x)).preimage r.continuous),
    ⟨x, A.mem_neighborhood (r x), rfl⟩, ?_⟩
  exact ambientPathThin_image_preimage_of_homotopy r i H (A.ambientPathThin (r x))

namespace PathThinNeighborhoods

/-- Actual LPC converts open ambient-thin neighborhoods into the required open path components. -/
def ofOpenAmbientThin [LocallyPathConnectedSpace X]
    (h : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ AmbientPathThin U) :
    PathThinNeighborhoods X where
  neighborhood x := pathComponentIn (h x).choose x
  isOpen_neighborhood x := (h x).choose_spec.1.pathComponentIn x
  mem_neighborhood x := mem_pathComponentIn_self (h x).choose_spec.2.1
  isPathConnected_neighborhood x := isPathConnected_pathComponentIn (h x).choose_spec.2.1
  ambientPathThin x := (h x).choose_spec.2.2.mono pathComponentIn_subset

end PathThinNeighborhoods
end Topology
