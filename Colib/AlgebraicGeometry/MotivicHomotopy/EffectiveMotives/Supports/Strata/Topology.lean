/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.NoetherianSpace

/-! # Isolating the codimension strata of a Noetherian closed subset -/

public section

open Order Topology

namespace TopologicalSpace.Closeds

variable {X : Type*} [TopologicalSpace X]

/-- Every closed subset of a Noetherian sober space is a finite union of point closures. -/
theorem exists_finite_union_pointClosures [NoetherianSpace X] [QuasiSober X] (W : Closeds X) :
    ∃ S : Set X, S.Finite ∧ (W : Set X) = ⋃ x ∈ S, closure ({x} : Set X) := by
  obtain ⟨C, hC, hclosed, hirr, hW⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible W.isClosed
  let : Finite C := hC.to_subtype
  let pt (T : C) := (hirr T.1 T.2).genericPoint
  have hpt (T : C) : closure ({pt T} : Set X) = T.1 :=
    (hirr T.1 T.2).closure_genericPoint (hclosed T.1 T.2)
  refine ⟨Set.range pt, Set.finite_range pt, ?_⟩
  ext y
  rw [hW, Set.mem_sUnion, Set.mem_iUnion₂]
  constructor
  · rintro ⟨T, hT, hy⟩
    exact ⟨pt ⟨T, hT⟩, Set.mem_range_self _, hpt ⟨T, hT⟩ ▸ hy⟩
  · rintro ⟨_, ⟨T, rfl⟩, hy⟩
    exact ⟨T.1, T.2, hpt T ▸ hy⟩

variable [T0Space X]

attribute [local instance] specializationOrder

/-- Specialization preserves each lower bound on point codimension. -/
theorem le_coheight_of_mem_pointClosure {x y : X} (hxy : y ∈ closure ({x} : Set X))
    {p : ℕ} (hx : (p : ℕ∞) ≤ coheight x) : (p : ℕ∞) ≤ coheight y :=
  hx.trans (coheight_anti ((specializes_iff_mem_closure).2 hxy))

/-- A proper specialization raises each finite lower bound on point codimension. -/
theorem succ_le_coheight_of_mem_pointClosure {x y : X} (hxy : y ∈ closure ({x} : Set X))
    (hyx : y ≠ x) {p : ℕ} (hx : (p : ℕ∞) ≤ coheight x) :
    ((p + 1 : ℕ) : ℕ∞) ≤ coheight y := by
  have hle : y ≤ x := (specializes_iff_mem_closure).2 hxy
  rw [Nat.cast_add, Nat.cast_one]
  calc
    (p : ℕ∞) + 1 ≤ coheight x + 1 := by gcongr
    _ ≤ coheight y := coheight_add_one_le (lt_of_le_of_ne hle hyx)

/-- A presentation of a support by finitely many point closures contains every point
of the minimal allowed codimension. -/
theorem mem_of_coheight_eq_of_eq_union_pointClosures {W : Closeds X} {S : Set X}
    (hW : (W : Set X) = ⋃ x ∈ S, closure ({x} : Set X)) {p : ℕ}
    (hp : ∀ x ∈ (W : Set X), (p : ℕ∞) ≤ coheight x)
    {x : X} (hx : x ∈ (W : Set X)) (hx' : coheight x = p) : x ∈ S := by
  have hxU := Set.mem_iUnion₂.mp (hW ▸ hx)
  obtain ⟨z, hz, hxz⟩ := hxU
  have hzW : z ∈ (W : Set X) := by
    rw [hW]
    exact Set.mem_iUnion₂.mpr ⟨z, hz, subset_closure (Set.mem_singleton z)⟩
  by_contra hn
  have hne : x ≠ z := fun h ↦ hn (h.symm ▸ hz)
  have hc := succ_le_coheight_of_mem_pointClosure hxz hne (hp z hzW)
  rw [hx', ENat.natCast_le_natCast] at hc
  exact (Nat.not_succ_le_self p) hc

/-- A closed support bounded below by `p` contains only finitely many points of codimension `p`. -/
theorem finite_coheight_eq [NoetherianSpace X] [QuasiSober X]
    (W : Closeds X) {p : ℕ} (hp : ∀ x ∈ (W : Set X), (p : ℕ∞) ≤ coheight x) :
    {x : X | x ∈ (W : Set X) ∧ coheight x = p}.Finite := by
  obtain ⟨S, hS, hW⟩ := W.exists_finite_union_pointClosures
  exact hS.subset fun _ hx ↦ mem_of_coheight_eq_of_eq_union_pointClosures hW hp hx.1 hx.2

/-- The complement of a sufficiently large higher-codimension subset of a closed support is
covered by its codimension-`p` point closures, and a surviving point lies on exactly one of
these closures. -/
theorem exists_enlarge_for_disjoint_pointClosures [NoetherianSpace X] [QuasiSober X]
    {Z W : Closeds X} (hZW : Z ≤ W) {p : ℕ}
    (hZ : ∀ x ∈ (Z : Set X), ((p + 1 : ℕ) : ℕ∞) ≤ coheight x)
    (hW : ∀ x ∈ (W : Set X), (p : ℕ∞) ≤ coheight x) :
    ∃ Z' : Closeds X, Z ≤ Z' ∧ Z' ≤ W ∧
      (∀ x ∈ (Z' : Set X), ((p + 1 : ℕ) : ℕ∞) ≤ coheight x) ∧
      ∀ y ∈ (W : Set X) \ (Z' : Set X),
        ∃! x : {x : X // x ∈ (W : Set X) ∧ coheight x = p},
          y ∈ closure ({x.1} : Set X) := by
  classical
  obtain ⟨S, hSf, hS⟩ := W.exists_finite_union_pointClosures
  have hsub (x : X) (hx : x ∈ S) : closure ({x} : Set X) ⊆ W := by
    rw [hS]
    exact Set.subset_iUnion₂_of_subset x hx subset_rfl
  let B := ⋃ x ∈ {x ∈ S | ((p + 1 : ℕ) : ℕ∞) ≤ coheight x}, closure ({x} : Set X)
  let D := ⋃ ij ∈ {ij ∈ S ×ˢ S | ij.1 ≠ ij.2},
    closure ({ij.1} : Set X) ∩ closure ({ij.2} : Set X)
  have hBc : IsClosed B :=
    (hSf.subset (fun _ hx ↦ hx.1)).isClosed_biUnion (fun _ _ ↦ isClosed_closure)
  have hDc : IsClosed D :=
    ((hSf.prod hSf).subset (fun _ hij ↦ hij.1)).isClosed_biUnion
      (fun _ _ ↦ isClosed_closure.inter isClosed_closure)
  refine ⟨Z ⊔ ⟨B ∪ D, hBc.union hDc⟩, le_sup_left, sup_le hZW ?_, ?_, ?_⟩
  · rintro y (hy | hy)
    · obtain ⟨x, hx, hxy⟩ := Set.mem_iUnion₂.mp hy
      exact hsub x hx.1 hxy
    · obtain ⟨ij, hij, hyij⟩ := Set.mem_iUnion₂.mp hy
      exact hsub ij.1 hij.1.1 hyij.1
  · intro y hy
    rw [Closeds.coe_sup] at hy
    rcases hy with hy | hy | hy
    · exact hZ y hy
    · obtain ⟨x, hx, hxy⟩ := Set.mem_iUnion₂.mp hy
      exact le_coheight_of_mem_pointClosure hxy hx.2
    · obtain ⟨ij, hij, hyij⟩ := Set.mem_iUnion₂.mp hy
      have hco (a : X) (ha : a ∈ S) : (p : ℕ∞) ≤ coheight a :=
        hW a (hsub a ha (subset_closure (Set.mem_singleton _)))
      by_cases he : y = ij.1
      · exact succ_le_coheight_of_mem_pointClosure hyij.2 (he.trans_ne hij.2) (hco _ hij.1.2)
      · exact succ_le_coheight_of_mem_pointClosure hyij.1 he (hco _ hij.1.1)
  · rintro y ⟨hyW, hy⟩
    have hyB : y ∉ B := fun h ↦ hy (Or.inr (Or.inl h))
    have hyD : y ∉ D := fun h ↦ hy (Or.inr (Or.inr h))
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.mp (hS ▸ hyW)
    have hxW : x ∈ (W : Set X) := hsub x hx (subset_closure (Set.mem_singleton _))
    have hxlt : coheight x < ((p + 1 : ℕ) : ℕ∞) :=
      lt_of_not_ge (fun h ↦ hyB (Set.mem_iUnion₂.mpr ⟨x, ⟨hx, h⟩, hyx⟩))
    have hxp : coheight x = ↑p := by
      obtain ⟨a, hxa, ha⟩ := ENat.le_natCast_iff.mp hxlt.le
      rw [hxa, ENat.natCast_lt_natCast] at hxlt
      have hap := hW x hxW
      rw [hxa, ENat.natCast_le_natCast] at hap
      exact hxa.trans (congrArg Nat.cast (le_antisymm (Nat.lt_succ_iff.mp hxlt) hap))
    refine ⟨⟨x, hxW, hxp⟩, hyx, fun z hyz ↦ Subtype.ext ?_⟩
    by_contra hne
    have hzS := mem_of_coheight_eq_of_eq_union_pointClosures hS hW z.2.1 z.2.2
    exact hyD (Set.mem_iUnion₂.mpr ⟨(z.1, x), ⟨⟨hzS, hx⟩, hne⟩, hyz, hyx⟩)

/-- A point in the lowest codimension stratum has an open neighbourhood on which
its closure is the whole support. The open can avoid any higher-codimension subset. -/
theorem exists_open_isolating_pointClosure [NoetherianSpace X] [QuasiSober X]
    {Z W : Closeds X} {p : ℕ}
    (hZ : ∀ y ∈ (Z : Set X), ((p + 1 : ℕ) : ℕ∞) ≤ coheight y)
    (hW : ∀ y ∈ (W : Set X), (p : ℕ∞) ≤ coheight y)
    {x : X} (hxW : x ∈ (W : Set X)) (hx : coheight x = (p : ℕ∞)) :
    ∃ U : Opens X, x ∈ U ∧ U ≤ Z.compl ∧
      U ⊓ (Closeds.closure {x}).compl = U ⊓ W.compl := by
  classical
  obtain ⟨S, hSf, hS⟩ := W.exists_finite_union_pointClosures
  have hsub (z : X) (hz : z ∈ S) : closure ({z} : Set X) ⊆ W := by
    rw [hS]
    exact Set.subset_iUnion₂_of_subset z hz subset_rfl
  let D := ⋃ z ∈ S \ {x}, closure ({z} : Set X)
  have hfin : (S \ {x}).Finite := hSf.sdiff
  have hD : IsClosed D := hfin.isClosed_biUnion (fun _ _ ↦ isClosed_closure)
  let U : Opens X := (Z ⊔ ⟨D, hD⟩).compl
  have hxZ : x ∉ (Z : Set X) := by
    intro h
    have hc := hZ x h
    rw [hx, ENat.natCast_le_natCast] at hc
    exact (Nat.not_succ_le_self _) hc
  have hxD : x ∉ D := by
    intro hh
    obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp hh
    have hzc := hW z (hsub z hz.1 (subset_closure (Set.mem_singleton z)))
    have hzx : x ≠ z := Ne.symm (Set.notMem_singleton_iff.mp hz.2)
    have hc := succ_le_coheight_of_mem_pointClosure hxz hzx hzc
    rw [hx, ENat.natCast_le_natCast] at hc
    exact (Nat.not_succ_le_self _) hc
  refine ⟨U, fun h ↦ h.elim hxZ hxD, Set.compl_subset_compl.mpr le_sup_left, ?_⟩
  ext y
  change (y ∈ U ∧ y ∉ closure {x}) ↔ (y ∈ U ∧ y ∉ (W : Set X))
  constructor
  · rintro ⟨hyU, hyC⟩
    refine ⟨hyU, fun hyW ↦ ?_⟩
    obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.mp (hS ▸ hyW)
    by_cases hzx : z = x
    · exact hyC (hzx ▸ hyz)
    · exact hyU (Or.inr (Set.mem_iUnion₂.mpr ⟨z, ⟨hz, hzx⟩, hyz⟩))
  · rintro ⟨hyU, hyW⟩
    exact ⟨hyU, fun hyC ↦ hyW (closure_minimal (Set.singleton_subset_iff.mpr hxW)
      W.isClosed hyC)⟩

/-- Open charts isolating a finite collection of disjoint point closures over a punctured open.
The common complementary open is included even if the collection is empty. -/
theorem exists_disjoint_pointClosure_openCover {Z W : Closeds X} {p : ℕ}
    (hZW : Z ≤ W) (hZ : ∀ y ∈ (Z : Set X), ((p + 1 : ℕ) : ℕ∞) ≤ coheight y)
    [Finite {x : X // x ∈ (W : Set X) ∧ coheight x = p}]
    (hgood : ∀ y ∈ (W : Set X) \ (Z : Set X),
      ∃! x : {x : X // x ∈ (W : Set X) ∧ coheight x = p},
        y ∈ closure ({x.1} : Set X)) :
    let I := {x : X // x ∈ (W : Set X) ∧ coheight x = p}
    ∃ V : I → Opens X,
      (∀ i, i.1 ∈ V i) ∧ (∀ i, W.compl ≤ V i) ∧ (∀ i, V i ≤ Z.compl) ∧
      Z.compl ≤ W.compl ⊔ iSup V ∧ (∀ i j, i ≠ j → V i ⊓ V j ≤ W.compl) ∧
      (∀ i, V i ⊓ (Closeds.closure {i.1}).compl = W.compl) ∧
      (∀ i, (Z.compl ⊓ (Closeds.closure {i.1}).compl) ⊔ V i = Z.compl) := by
  classical
  let I := {x : X // x ∈ (W : Set X) ∧ coheight x = p}
  let C (i : I) := closure ({i.1} : Set X)
  let D (i : I) := ⋃ j : {j : I // j ≠ i}, C j.1
  let V (i : I) : Opens X :=
    (Z ⊔ (⟨D i, isClosed_iUnion_of_finite (fun _ ↦ isClosed_closure)⟩ : Closeds X)).compl
  have hCW (i : I) : C i ⊆ W :=
    closure_minimal (Set.singleton_subset_iff.mpr i.2.1) W.isClosed
  have hxZ (i : I) : i.1 ∉ (Z : Set X) := by
    intro h
    have hc := hZ i.1 h
    rw [i.2.2, ENat.natCast_le_natCast] at hc
    exact (Nat.not_succ_le_self _) hc
  have hV (i : I) (y : X) :
      y ∈ V i ↔ y ∉ (Z : Set X) ∧ ∀ j : I, j ≠ i → y ∉ C j := by
    change (¬(y ∈ (Z : Set X) ∨ y ∈ D i)) ↔ _
    constructor
    · intro h
      refine ⟨fun hz ↦ h (Or.inl hz), fun j hji hyj ↦ ?_⟩
      exact h (Or.inr (Set.mem_iUnion.mpr ⟨⟨j, hji⟩, hyj⟩))
    · rintro ⟨hnZ, hnD⟩ (hZ | hD)
      · exact hnZ hZ
      · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hD
        exact hnD j.1 j.2 hj
  have hVi (i : I) : i.1 ∈ V i := by
    refine (hV i _).mpr ⟨hxZ i, fun j hij h ↦ ?_⟩
    have hc := succ_le_coheight_of_mem_pointClosure h
      (fun he ↦ hij (Subtype.ext he.symm)) j.2.2.ge
    rw [i.2.2, ENat.natCast_le_natCast] at hc
    exact (Nat.not_succ_le_self _) hc
  have hBV (i : I) : W.compl ≤ V i := fun y hy ↦
    (hV i y).mpr ⟨fun hz ↦ hy (hZW hz), fun j _ hj ↦ hy (hCW j hj)⟩
  have hVZ (i : I) : V i ≤ Z.compl := fun y hy ↦ ((hV i y).mp hy).1
  have hto (i : I) {y : X} (hy : y ∈ V i) (hyW : y ∈ (W : Set X)) : y ∈ C i := by
    obtain ⟨j, hyj, _⟩ := hgood y ⟨hyW, hVZ i hy⟩
    by_cases h : j = i
    · exact h ▸ hyj
    · exact False.elim (((hV i y).mp hy).2 j h hyj)
  have hfrom (i : I) {y : X} (hyZ : y ∈ Z.compl) (hy : y ∈ C i) : y ∈ V i := by
    obtain ⟨j, _, hunique⟩ := hgood y ⟨hCW i hy, hyZ⟩
    exact (hV i y).mpr ⟨hyZ, fun t ht hyt ↦ ht ((hunique t hyt).trans (hunique i hy).symm)⟩
  refine ⟨V, hVi, hBV, hVZ, ?_, ?_, ?_, ?_⟩
  · intro y hy
    by_cases hyW : y ∈ (W : Set X)
    · obtain ⟨i, hi, _⟩ := hgood y ⟨hyW, hy⟩
      exact Or.inr (Opens.mem_iSup.mpr ⟨i, hfrom i hy hi⟩)
    · exact Or.inl hyW
  · rintro i j hij y ⟨hi, hj⟩ hyW
    exact ((hV j y).mp hj).2 i hij (hto i hi hyW)
  · intro i
    apply le_antisymm
    · rintro y ⟨hy, hn⟩ hW
      exact hn (hto i hy hW)
    · intro y hy
      exact ⟨hBV i hy, fun h ↦ hy (hCW i h)⟩
  · intro i
    refine le_antisymm (sup_le inf_le_left (hVZ i)) ?_
    intro y hy
    by_cases h : y ∈ C i
    · exact Or.inr (hfrom i hy h)
    · exact Or.inl ⟨hy, h⟩

end TopologicalSpace.Closeds
