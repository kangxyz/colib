/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.Telescope
public import Colib.Topology.Prespectrum.HomotopyLoop
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Collapsing a finite initial string of original telescope cylinders

Finite composites of the original transition maps and continuous cylinder sweeps
contract each finite prefix toward its last original stage. Every sweep is
constructed on the unchanged reduced quotient by compact-open currying.
-/
@[expose] public section

noncomputable section
open CategoryTheory
open scoped Topology unitInterval
open unitInterval
universe u
namespace Topology.LoopPrespectrum.Telescope
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))

/-- The finite composite of original connecting maps. -/
def transition (i j : ℕ) (h : i ≤ j) : E i ⟶ E j := Functor.OfSequence.map f i j h

@[simp] theorem transition_refl (i : ℕ) : transition E f i i le_rfl = 𝟙 (E i) :=
  Functor.OfSequence.map_id f i

@[simp] theorem transition_succ (i : ℕ) :
    transition E f i (i + 1) (Nat.le_succ i) = f i := Functor.OfSequence.map_le_succ f i

/-- Finite composites preserve their original factorization through an intermediate stage. -/
theorem transition_comp (i j l : ℕ) (hij : i ≤ j) (hjl : j ≤ l) :
    transition E f i l (hij.trans hjl) = transition E f i j hij ≫ transition E f j l hjl :=
  Functor.OfSequence.map_comp f i j l hij hjl

/-- A single continuous cylinder sweep after the earlier cylinders have collapsed. -/
def sweepPiece (N k i : ℕ) : C(I × (E i).space k, C(I, Space E f k)) :=
  if h : i ≤ N then
    ContinuousMap.curry
      ⟨fun z ↦ cylinder E f k N
        ((if i < N then z.2 else max z.1.1 z.2), (transition E f i N h).map k z.1.2), by
          split_ifs <;> fun_prop⟩
  else
    ContinuousMap.curry ⟨fun z ↦ cylinder E f k i z.1, by fun_prop⟩

/-- Earlier cylinders move together along the current original stage cylinder. -/
theorem sweepPiece_of_lt {N i : ℕ} (hi : i < N) (k : ℕ) (z : I × (E i).space k) (t : I) :
    sweepPiece E f N k i z t =
      cylinder E f k N (t, (transition E f i N hi.le).map k z.2) := by
  simp [sweepPiece, hi, hi.le]

/-- The current cylinder contracts by moving its coordinate upward. -/
theorem sweepPiece_self (N k : ℕ) (z : I × (E N).space k) (t : I) :
    sweepPiece E f N k N z t = cylinder E f k N (max z.1 t, z.2) := by
  simp only [sweepPiece, le_refl, ↓reduceDIte, ContinuousMap.curry_apply,
    ContinuousMap.coe_mk, lt_self_iff_false, ↓reduceIte, transition_refl]
  rfl

/-- Later original cylinders remain fixed during a finite-prefix sweep. -/
theorem sweepPiece_of_gt {N i : ℕ} (hi : N < i) (k : ℕ) (z : I × (E i).space k) (t : I) :
    sweepPiece E f N k i z t = cylinder E f k i z := by
  simp [sweepPiece, Nat.not_le.mpr hi]

/-- The sweep descends through the original gluing and collapsed ray. -/
theorem sweepPiece_respects (N k : ℕ) {z w : Σ i, I × (E i).space k}
    (h : Relation E f k z w) : sweepPiece E f N k z.1 z.2 = sweepPiece E f N k w.1 w.2 := by
  ext t
  cases h with
  | step i x =>
    rcases lt_trichotomy i N with hi | rfl | hi
    · rw [sweepPiece_of_lt E f hi]
      have hmap : (transition E f i N hi.le).map k x =
          (transition E f (i + 1) N hi).map k ((f i).map k x) := by
        rw [transition_comp E f i (i + 1) N (Nat.le_succ i) hi, transition_succ]
        rfl
      rcases lt_or_eq_of_le (show i + 1 ≤ N from hi) with hi' | hEq
      · rw [sweepPiece_of_lt E f hi', hmap]
      · subst N
        rw [sweepPiece_self, max_eq_right unitInterval.nonneg', hmap, transition_refl]
        rfl
    · rw [sweepPiece_self, max_eq_left unitInterval.le_one', cylinder_one,
        sweepPiece_of_gt E f (Nat.lt_succ_self i)]
    · rw [sweepPiece_of_gt E f hi, sweepPiece_of_gt E f (hi.trans (Nat.lt_succ_self i)),
        cylinder_one]
  | base i s =>
    have hbase (i : ℕ) (s : I) : sweepPiece E f N k i (s, (E i).point k) t = point E f k := by
      rcases lt_trichotomy i N with hi | rfl | hi
      · rw [sweepPiece_of_lt E f hi, (transition E f i N hi.le).map_point, cylinder_point]
      · rw [sweepPiece_self, cylinder_point]
      · rw [sweepPiece_of_gt E f hi, cylinder_point]
    exact (hbase i s).trans (hbase 0 0).symm

/-- Descend interval-valued maps before evaluating sweep time. -/
def sweepFamily (N k : ℕ) : C(Space E f k, C(I, Space E f k)) where
  toFun := Quot.lift (fun z ↦ sweepPiece E f N k z.1 z.2)
    (fun _ _ ↦ sweepPiece_respects E f N k)
  continuous_toFun := continuous_quot_lift _
    (continuous_sigma (fun i ↦ (sweepPiece E f N k i).continuous))

@[simp] theorem sweepFamily_cylinder (N k i : ℕ) (z : I × (E i).space k) (t : I) :
    sweepFamily E f N k (cylinder E f k i z) t = sweepPiece E f N k i z t := rfl

/-- Every sweep fixes the original reduced basepoint at every time. -/
@[simp] theorem sweepFamily_point (N k : ℕ) (t : I) :
    sweepFamily E f N k (point E f k) t = point E f k := by
  change sweepPiece E f N k 0 (0, (E 0).point k) t = _
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [sweepPiece_self, cylinder_point]
  · rw [sweepPiece_of_lt E f hN, (transition E f 0 N hN.le).map_point, cylinder_point]

/-- Sweep time remains independent of the original prespectrum structure time. -/
theorem sweepFamily_comm (N k : ℕ) (q : Space E f k) (s t : I) :
    sweepFamily E f N (k + 1) (structureMap E f k q t) s =
      structureMap E f k (sweepFamily E f N k q s) t := by
  induction q using Quot.inductionOn with
  | h z =>
    obtain ⟨i, r, x⟩ := z
    change sweepFamily E f N (k + 1)
      (cylinder E f (k + 1) i (r, (E i).structureMap k x t)) s =
        structureMap E f k (sweepFamily E f N k (cylinder E f k i (r, x)) s) t
    simp only [sweepFamily_cylinder]
    rcases lt_trichotomy i N with hi | rfl | hi
    · rw [sweepPiece_of_lt E f hi, sweepPiece_of_lt E f hi, structureMap_cylinder]
      exact congrArg (fun y ↦ cylinder E f (k + 1) N (s, y))
        (congrArg (fun p ↦ p t) ((transition E f i N hi.le).comm k x))
    · rw [sweepPiece_self, sweepPiece_self, structureMap_cylinder]
    · rw [sweepPiece_of_gt E f hi, sweepPiece_of_gt E f hi, structureMap_cylinder]

/-- Every sweep-time slice is an actual based prespectrum map. -/
def sweepMap (N : ℕ) (t : I) : prespectrum E f ⟶ prespectrum E f where
  map k := ⟨fun q ↦ sweepFamily E f N k q t,
    (sweepFamily E f N k).uncurry.continuous.comp
      (continuous_id.prodMk continuous_const)⟩
  map_point k := sweepFamily_point E f N k t
  comm k q := by
    ext s
    exact sweepFamily_comm E f N k q t s

/-- Collapse the first N original cylinders and fix the remaining tail. -/
def collapse (N : ℕ) : prespectrum E f ⟶ prespectrum E f := sweepMap E f N 0

/-- Earlier whole cylinders are sent to the original stage-N inclusion. -/
theorem collapse_cylinder_of_lt {N i : ℕ} (hi : i < N) (k : ℕ) (z : I × (E i).space k) :
    (collapse E f N).map k (cylinder E f k i z) =
      (inclusion E f N).map k ((transition E f i N hi.le).map k z.2) :=
  sweepPiece_of_lt E f hi k z 0

/-- The original tail cylinders are fixed pointwise. -/
theorem collapse_cylinder_of_le {N i : ℕ} (hi : N ≤ i) (k : ℕ) (z : I × (E i).space k) :
    (collapse E f N).map k (cylinder E f k i z) = cylinder E f k i z := by
  change sweepPiece E f N k i z 0 = _
  rcases lt_or_eq_of_le hi with hi | rfl
  · exact sweepPiece_of_gt E f hi k z 0
  · rw [sweepPiece_self, max_eq_left unitInterval.nonneg']

@[simp] theorem collapse_zero : collapse E f 0 = 𝟙 (prespectrum E f) := by
  apply hom_ext
  intro k i s x
  exact collapse_cylinder_of_le E f (Nat.zero_le i) k (s, x)

/-- On every earlier original stage, collapse is exactly its original finite transition. -/
theorem collapse_inclusion {N i : ℕ} (hi : i ≤ N) (k : ℕ) (x : (E i).space k) :
    (collapse E f N).map k ((inclusion E f i).map k x) =
      (inclusion E f N).map k ((transition E f i N hi).map k x) := by
  rcases lt_or_eq_of_le hi with hi | rfl
  · exact collapse_cylinder_of_lt E f hi k (0, x)
  · rw [transition_refl]
    exact collapse_cylinder_of_le E f le_rfl k (0, x)

/-- The end of one sweep is the start of the next finite-prefix collapse. -/
theorem sweepMap_one (N : ℕ) : sweepMap E f N 1 = collapse E f (N + 1) := by
  apply hom_ext
  intro k i s x
  change sweepPiece E f N k i (s, x) 1 = _
  rcases lt_trichotomy i N with hi | rfl | hi
  · rw [sweepPiece_of_lt E f hi, cylinder_one,
      collapse_cylinder_of_lt E f (hi.trans (Nat.lt_succ_self N))]
    rw [transition_comp E f i N (N + 1) hi.le (Nat.le_succ N), transition_succ]
    rfl
  · rw [sweepPiece_self, max_eq_right unitInterval.le_one', cylinder_one,
      collapse_cylinder_of_lt E f (Nat.lt_succ_self i), transition_succ]
    rfl
  · rw [sweepPiece_of_gt E f hi, collapse_cylinder_of_le E f hi]

/-- Sweep the next cylinder through a based, structure-compatible homotopy. -/
def sweepHomotopy (N : ℕ) : Homotopy (collapse E f N) (collapse E f (N + 1)) where
  level k := ⟨fun z ↦ sweepFamily E f N k z.2 z.1,
    (sweepFamily E f N k).uncurry.continuous.comp continuous_swap⟩
  at_zero _k _q := rfl
  at_one k q := congrArg (fun h ↦ h.map k q) (sweepMap_one E f N)
  at_point k s := sweepFamily_point E f N k s
  comm k s q t := sweepFamily_comm E f N k q s t

/-- The actual identity is coherently based-homotopic to every finite-prefix collapse. -/
def collapseHomotopy : (N : ℕ) → Homotopy (𝟙 (prespectrum E f)) (collapse E f N)
  | 0 => (collapse_zero E f).symm ▸ Homotopy.refl (𝟙 (prespectrum E f))
  | N + 1 => (collapseHomotopy N).trans (sweepHomotopy E f N)

/-- The original stage map and its finite transition into a later stage are coherently homotopic. -/
def inclusionTransitionHomotopy {i N : ℕ} (hi : i ≤ N) :
    Homotopy (inclusion E f i) (transition E f i N hi ≫ inclusion E f N) := by
  have hc : inclusion E f i ≫ collapse E f N = transition E f i N hi ≫ inclusion E f N := by
    apply Hom.ext
    funext k
    ext x
    exact collapse_inclusion E f hi k x
  simpa only [Category.comp_id, hc] using
    Homotopy.precomp (inclusion E f i) (collapseHomotopy E f N)

/-- Finite transition compatibility holds for the actual original homotopy-group maps. -/
theorem inclusion_transition_homotopyGroupMap {i N : ℕ} (hi : i ≤ N) (k n : ℕ)
    (a : HomotopyGroup.Pi n ((E i).space k) ((E i).point k)) :
    HomotopyGroup.map ((inclusion E f i).map k) ((inclusion E f i).map_point k) a =
      HomotopyGroup.map ((inclusion E f N).map k) ((inclusion E f N).map_point k)
        (HomotopyGroup.map ((transition E f i N hi).map k)
          ((transition E f i N hi).map_point k) a) := by
  exact (congrFun ((inclusionTransitionHomotopy E f hi).homotopyGroupMap_eq k n) a).trans
    (HomotopyGroup.map_comp ((transition E f i N hi).map k)
      ((transition E f i N hi).map_point k) ((inclusion E f N).map k)
      ((inclusion E f N).map_point k) a)

end Topology.LoopPrespectrum.Telescope
