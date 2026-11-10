/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy

/-!
# Nonadditive paths and the native alternating-face complex

A zero-preserving, face-compatible function may be chosen on each chain group;
no additivity of these choices is required. Applied to a normalized cycle, the
chosen path is still a cycle. A simplicial homotopy between its two endpoint
maps then supplies an actual boundary, with Mathlib's native sign convention.
The actual Moore inclusion is a homotopy equivalence, so this kills homology in
every degree, including zero.

Adapted from `SingularComplex/NormalizedCycleFaces`, `NormalizedCyclePaths`,
`SetwisePaths` and the cycle-boundary lemma of `Endpoints` in
`kangxyz/motivic` at a6805c4a87cdfd7717dd7a94039246a167f15380.
Only Mathlib's existing complexes are used; no singular-complex wrapper is
introduced here.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite
open scoped Simplicial

universe u w

namespace HomologicalComplex

/-- A chain map whose every cycle is sent to a boundary is zero on homology. -/
theorem homologyMap_eq_zero_of_cycle_boundaries
    {K L : ChainComplex AddCommGrpCat.{w} ℕ} (α : K ⟶ L) (n : ℕ)
    (h : ∀ x : K.X n, (∀ m, K.d n m x = 0) →
      ∃ y : L.X (n + 1), L.d (n + 1) n y = α.f n x) :
    HomologicalComplex.homologyMap α n = 0 := by
  apply (cancel_epi (K.homologyπ n)).mp
  rw [HomologicalComplex.homologyπ_naturality, comp_zero]
  ext x
  obtain ⟨y, hy⟩ := h (K.iCycles n x) (fun m =>
    ConcreteCategory.congr_hom (K.iCycles_d n m) x)
  have hc : HomologicalComplex.cyclesMap α n x = L.toCycles (n + 1) n y := by
    apply (AddCommGrpCat.mono_iff_injective (L.iCycles n)).mp inferInstance
    have hl := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i α n) x
    have hr := ConcreteCategory.congr_hom (L.toCycles_i (n + 1) n) y
    exact hl.trans (hy.symm.trans hr.symm)
  change L.homologyπ n (HomologicalComplex.cyclesMap α n x) = 0
  rw [hc, ← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_comp_homologyπ]
  rfl

/-- A cycle joining zero to a given endpoint supplies an explicit boundary.
The lift may be chosen nonlinearly: no additive contraction is assumed. -/
theorem boundary_of_cycle_path {D E : ChainComplex AddCommGrpCat.{w} ℕ}
    {f g : D ⟶ E} (H : _root_.Homotopy f g) (n : ℕ) (y : D.X n)
    (hy : ∀ m, D.d n m y = 0) (hf : f.f n y = 0) :
    E.d (n + 1) n (-(H.hom n (n + 1) y)) = g.f n y := by
  have hc := H.comm n
  rw [prevD_eq H.hom (j := n) (j' := n + 1) (by simp)] at hc
  have he := ConcreteCategory.congr_hom hc y
  change f.f n y = H.hom _ n (D.d n _ y) + E.d (n + 1) n (H.hom n (n + 1) y) +
    g.f n y at he
  rw [hy, map_zero, zero_add, hf] at he
  rw [_root_.map_neg]
  exact (eq_neg_of_add_eq_zero_right he.symm).symm

end HomologicalComplex

namespace CategoryTheory.SimplicialObject

/-- In the actual normalized Moore complex, the zeroth face is its differential. -/
theorem normalized_zero_face (S : SimplicialObject AddCommGrpCat.{u}) (n : ℕ) :
    (inclusionOfMooreComplexMap S).f (n + 1) ≫ S.δ 0 =
      ((normalizedMooreComplex AddCommGrpCat).obj S).d (n + 1) n ≫
        (inclusionOfMooreComplexMap S).f n := by
  rw [normalizedMooreComplex_objD]
  simp only [inclusionOfMooreComplexMap_f]
  cases n <;> simp [NormalizedMooreComplex.objD]

/-- All faces of an actual normalized cycle vanish, including the zeroth face. -/
theorem normalized_cycle_faces (S : SimplicialObject AddCommGrpCat.{u}) (n : ℕ)
    (x : ((normalizedMooreComplex AddCommGrpCat).obj S).X (n + 1))
    (hx : ((normalizedMooreComplex AddCommGrpCat).obj S).d (n + 1) n x = 0)
    (i : Fin (n + 2)) :
    S.δ i ((inclusionOfMooreComplexMap S).f (n + 1) x) = 0 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · have h := ConcreteCategory.congr_hom (normalized_zero_face S n) x
    change S.δ 0 ((inclusionOfMooreComplexMap S).f (n + 1) x) =
      (inclusionOfMooreComplexMap S).f n
        (((normalizedMooreComplex AddCommGrpCat).obj S).d (n + 1) n x) at h
    rw [hx, map_zero] at h
    exact h
  · exact ConcreteCategory.congr_hom
      (DoldKan.HigherFacesVanish.inclusionOfMooreComplexMap (X := S) n j (by omega)) x

/-- A chain with every face zero is a cycle for the native alternating differential. -/
theorem cycle_of_faces_zero (S : SimplicialObject AddCommGrpCat.{u})
    (n : ℕ) (x : ((alternatingFaceMapComplex AddCommGrpCat).obj S).X n)
    (h : ∀ m (e : n = m + 1) (i : Fin (m + 2)), S.δ i (e ▸ x) = 0) :
    ∀ m, ((alternatingFaceMapComplex AddCommGrpCat).obj S).d n m x = 0 := by
  intro m
  by_cases e : n = m + 1
  · subst n
    change (AlternatingFaceMapComplex.obj S).d (m + 1) m x = 0
    rw [AlternatingFaceMapComplex.obj_d_eq]
    let ev : (S.obj (op ⦋m + 1⦌) ⟶ S.obj (op ⦋m⦌)) →+ S.obj (op ⦋m⦌) :=
      (AddMonoidHom.eval x).comp AddCommGrpCat.homAddEquiv.toAddMonoidHom
    change ev (∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) • S.δ i) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i _
    change (((-1 : ℤ) ^ (i : ℕ) • S.δ i).hom) x = 0
    simp only [AddCommGrpCat.hom_zsmul, AddMonoidHom.zsmul_apply, h m rfl i, smul_zero]
  · rw [((alternatingFaceMapComplex AddCommGrpCat).obj S).shape n m
      (by simpa [eq_comm] using e)]
    rfl

/-- Face-compatible setwise paths from zero to each chain kill all homology.
The endpoint maps are simplicially homotopic; the chosen path function need
not preserve addition, and only face compatibility is required of it. -/
theorem isZero_homology_of_setwise_paths
    {S T : SimplicialObject AddCommGrpCat.{u}} {f g : T ⟶ S}
    (H : Homotopy f g)
    (path : ∀ n, S.obj (op ⦋n⦌) → T.obj (op ⦋n⦌))
    (path_zero : ∀ n, path n 0 = 0)
    (path_face : ∀ n (i : Fin (n + 2)) (x : S.obj (op ⦋n + 1⦌)),
      T.δ i (path (n + 1) x) = path n (S.δ i x))
    (path_start : ∀ n x, f.app (op ⦋n⦌) (path n x) = 0)
    (path_end : ∀ n x, g.app (op ⦋n⦌) (path n x) = x)
    (n : ℕ) : IsZero (((alternatingFaceMapComplex AddCommGrpCat).obj S).homology n) := by
  have hz : HomologicalComplex.homologyMap (inclusionOfMooreComplexMap S) n = 0 := by
    apply HomologicalComplex.homologyMap_eq_zero_of_cycle_boundaries
    intro x hx
    let z := (inclusionOfMooreComplexMap S).f n x
    let y := path n z
    have hy : ∀ m, ((alternatingFaceMapComplex AddCommGrpCat).obj T).d n m y = 0 := by
      apply cycle_of_faces_zero
      intro m e i
      subst n
      change T.δ i (path (m + 1) z) = 0
      rw [path_face]
      have hf : S.δ i z = 0 := normalized_cycle_faces S m x (hx m) i
      rw [hf, path_zero]
    refine ⟨-(H.toChainHomotopy.hom n (n + 1) y), ?_⟩
    exact (HomologicalComplex.boundary_of_cycle_path H.toChainHomotopy n y hy
      (path_start n z)).trans (path_end n z)
  let : QuasiIso (inclusionOfMooreComplexMap S) :=
    (DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y := S)).quasiIso_hom
  let : IsIso (HomologicalComplex.homologyMap (inclusionOfMooreComplexMap S) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).mp inferInstance
  exact (IsZero.iff_id_eq_zero _).mpr (by
    rw [← IsIso.inv_hom_id (HomologicalComplex.homologyMap (inclusionOfMooreComplexMap S) n)]
    simp only [hz, comp_zero])

end CategoryTheory.SimplicialObject
