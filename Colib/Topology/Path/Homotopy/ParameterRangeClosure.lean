/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.Topology.Path.Homotopy.ProjectionPasteWord

/-! Range preservation for the scalar operations used by the original Bass faces.
Adapted from Quillen’s `ParameterRangeClosure.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Topology unitInterval
universe u
namespace Path.Homotopy.ParameterSupport
variable {X : Type u} [TopologicalSpace X] {U : Set X} {a b c d : X}

/-- The assertion that every value of the path `p` lies in `U`. -/
def PathIn (U : Set X) {a b : X} (p : Path a b) : Prop := ∀ t, p t ∈ U
/-- The assertion that the entire path homotopy `J`, at every time and path parameter, lies in `U`.
-/
def HomotopyIn (U : Set X) {a b : X} {p q : Path a b} (J : p.Homotopy q) : Prop :=
  ∀ t, J t ∈ U

theorem path_symm {p : Path a b} (hp : PathIn U p) : PathIn U p.symm :=
  fun t ↦ hp (unitInterval.symm t)

theorem path_trans {p : Path a b} {q : Path b c} (hp : PathIn U p) (hq : PathIn U q) :
    PathIn U (p.trans q) := by
  intro t
  rw [Path.trans_apply]
  split_ifs
  · exact hp _
  · exact hq _

theorem path_trans_left {p : Path a b} {q : Path b c} (h : PathIn U (p.trans q)) :
    PathIn U p := by
  have h' : Set.range (p.trans q) ⊆ U := Set.range_subset_iff.mpr h
  rw [Path.trans_range] at h'
  exact Set.range_subset_iff.mp (Set.Subset.trans Set.subset_union_left h')

theorem path_trans_right {p : Path a b} {q : Path b c} (h : PathIn U (p.trans q)) :
    PathIn U q := by
  have h' : Set.range (p.trans q) ⊆ U := Set.range_subset_iff.mpr h
  rw [Path.trans_range] at h'
  exact Set.range_subset_iff.mp (Set.Subset.trans Set.subset_union_right h')

theorem path_cast {a' b' : X} {p : Path a b} (hp : PathIn U p)
    (ha : a' = a) (hb : b' = b) : PathIn U (p.cast ha hb) := hp

theorem hom_source {p q : Path a b} {J : p.Homotopy q} (hJ : HomotopyIn U J) :
    PathIn U p := by
  intro t
  simpa only [ContinuousMap.HomotopyWith.apply_zero, Path.coe_toContinuousMap] using hJ (0, t)

theorem hom_target {p q : Path a b} {J : p.Homotopy q} (hJ : HomotopyIn U J) :
    PathIn U q := by
  intro t
  simpa only [ContinuousMap.HomotopyWith.apply_one, Path.coe_toContinuousMap] using hJ (1, t)

theorem hom_refl {p : Path a b} (hp : PathIn U p) : HomotopyIn U (Path.Homotopy.refl p) :=
  fun t ↦ hp t.2

theorem hom_symm {p q : Path a b} {J : p.Homotopy q} (hJ : HomotopyIn U J) :
    HomotopyIn U J.symm := fun t ↦ hJ (unitInterval.symm t.1, t.2)

theorem hom_symm₂ {p q : Path a b} {J : p.Homotopy q} (hJ : HomotopyIn U J) :
    HomotopyIn U J.symm₂ := fun t ↦ hJ (t.1, unitInterval.symm t.2)

theorem hom_trans {p q r : Path a b} {J : p.Homotopy q} {K : q.Homotopy r}
    (hJ : HomotopyIn U J) (hK : HomotopyIn U K) : HomotopyIn U (J.trans K) := by
  intro t
  rw [Path.Homotopy.trans_apply]
  split_ifs
  · exact hJ _
  · exact hK _

theorem hom_hcomp {p q : Path a b} {r s : Path b c}
    {J : p.Homotopy q} {K : r.Homotopy s}
    (hJ : HomotopyIn U J) (hK : HomotopyIn U K) : HomotopyIn U (J.hcomp K) := by
  intro t
  rw [Path.Homotopy.hcomp_apply]
  split_ifs
  · exact hJ _
  · exact hK _

theorem hom_cast {p q p' q' : Path a b} {J : p.Homotopy q} (hJ : HomotopyIn U J)
    (hp : p = p') (hq : q = q') : HomotopyIn U (J.cast hp hq) := hJ

theorem hom_reparam {p : Path a b} (hp : PathIn U p) (f : unitInterval → unitInterval)
    (hf : Continuous f) (h₀ : f 0 = 0) (h₁ : f 1 = 1) :
    HomotopyIn U (Path.Homotopy.reparam p f hf h₀ h₁) := fun _ ↦ hp _

theorem hom_transRefl {p : Path a b} (hp : PathIn U p) :
    HomotopyIn U (Path.Homotopy.transRefl p) :=
  hom_symm (hom_cast (hom_reparam hp _ _ _ _) _ _)

theorem hom_reflTrans {p : Path a b} (hp : PathIn U p) :
    HomotopyIn U (Path.Homotopy.reflTrans p) :=
  hom_cast (hom_symm₂ (hom_transRefl (path_symm hp))) _ _

theorem hom_transAssoc {p : Path a b} {q : Path b c} {r : Path c d}
    (hp : PathIn U p) (hq : PathIn U q) (hr : PathIn U r) :
    HomotopyIn U (Path.Homotopy.transAssoc p q r) :=
  hom_symm (hom_cast (hom_reparam (path_trans hp (path_trans hq hr)) _ _ _ _) _ _)

theorem hom_reflTransSymm {p : Path a b} (hp : PathIn U p) :
    HomotopyIn U (Path.Homotopy.reflTransSymm p) := fun _ ↦ hp _

theorem hom_reflSymmTrans {p : Path a b} (hp : PathIn U p) :
    HomotopyIn U (Path.Homotopy.reflSymmTrans p) :=
  hom_cast (hom_reflTransSymm (path_symm hp)) _ _

/-- Actual path-equality transports retain the complete underlying scalar surface. -/
theorem hom_type_cast_apply {p q p' q' : Path a b} (hp : p = p') (hq : q = q')
    (ht : p.Homotopy q = p'.Homotopy q') (J : p.Homotopy q) (t : unitInterval × unitInterval) :
    (_root_.cast ht J) t = J t := by
  subst p'
  subst q'
  simp

end Path.Homotopy.ParameterSupport
