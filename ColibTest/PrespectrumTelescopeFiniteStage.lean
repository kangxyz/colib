/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.Topology.Prespectrum.TelescopeHomotopyColimit
import Colib.Topology.Prespectrum.TelescopeStableColimit
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Finite-stage and stable-colimit consumers

The discrete two-point cylinder has a genuine nonbase interior point, so its
finite-stage representative exists only up to homotopy. Degree zero remains a
homotopy set. The final tests use arbitrary integer stable degrees and arbitrary
classes; no nonzero stable group is claimed for the discrete example.
-/

open CategoryTheory CategoryTheory.Limits Topology Topology.LoopPrespectrum
open scoped Topology unitInterval

noncomputable section

namespace ColibTest.PrespectrumTelescopeFiniteStage

universe u

abbrev boolPrespectrum : LoopPrespectrum where
  space _ := TopCat.of Bool
  point _ := false
  structureMap _ := ContinuousMap.const _ (Path.refl false)
  map_point _ := rfl

abbrev stages (_ : ℕ) := boolPrespectrum

abbrev step (i : ℕ) : stages i ⟶ stages (i + 1) := 𝟙 boolPrespectrum

def projectionTrack (i : ℕ) :
    Homotopy (𝟙 boolPrespectrum) (step i ≫ 𝟙 boolPrespectrum) where
  level _ := ⟨fun z ↦ z.2, continuous_snd⟩
  at_zero _ _ := rfl
  at_one _ _ := rfl
  at_point _ _ := rfl
  comm _ _ _ _ := rfl

def projection : Telescope.prespectrum stages step ⟶ boolPrespectrum :=
  Telescope.desc stages step (fun _ ↦ 𝟙 boolPrespectrum) projectionTrack

def baseSubset : Set (unitInterval × Bool) := {z | z.2 = false}

example (k i : ℕ) : ∃ N, ∀ z : unitInterval × Bool,
    ∃ j ≤ N, ∃ w, Telescope.cylinder stages step k j w =
      Telescope.cylinder stages step k (i + 1) z :=
  Telescope.exists_cylinder_bound stages step k (Telescope.cylinder stages step k (i + 1))

example (k i : ℕ) : ∃ N, ∃ p : C(unitInterval × Bool, (stages N).space k),
    (∀ z ∈ baseSubset, p z = false) ∧
      Nonempty ((Telescope.cylinder stages step k (i + 1)).HomotopyRel
        (((Telescope.inclusion stages step N).map k).comp p) baseSubset) := by
  apply Telescope.exists_stage_representative stages step k baseSubset
  rintro ⟨s, b⟩ hb
  change b = false at hb
  subst b
  exact Telescope.cylinder_point stages step k (i + 1) s

def midpoint : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

lemma midpoint_ne_zero : midpoint ≠ 0 := by
  intro h
  have := congrArg (fun t : unitInterval ↦ (t : ℝ)) h
  norm_num [midpoint] at this

lemma midpoint_ne_one : midpoint ≠ 1 := by
  intro h
  have := congrArg (fun t : unitInterval ↦ (t : ℝ)) h
  norm_num [midpoint] at this

example (k i : ℕ) : Telescope.cylinder stages step k (i + 1) (midpoint, true) ≠
    Telescope.point stages step k := by
  intro h
  have hp := congrArg (projection.map k) h
  change true = false at hp
  cases hp

/-- In fact this interior point is outside every stage inclusion, not just earlier ones. -/
lemma midpoint_not_in_stage (k i N : ℕ) :
    Telescope.cylinder stages step k (i + 1) (midpoint, true) ∉
      Set.range ((Telescope.inclusion stages step N).map k) := by
  rintro ⟨b, hb⟩
  have hn := (Telescope.quot_eq_iff_normalForm_eq stages step k
    ⟨N, (0, b)⟩ ⟨i + 1, (midpoint, true)⟩).mp hb
  cases b with
  | false => simp [Telescope.normalForm, stages, boolPrespectrum, midpoint_ne_one] at hn
  | true =>
    have he : (⟨N, (0, true)⟩ : Σ j, unitInterval × (stages j).space k) =
        ⟨i + 1, (midpoint, true)⟩ := by
      simpa [Telescope.normalForm, stages, boolPrespectrum, midpoint_ne_one] using hn
    have ht := congrArg (fun z : Σ j, unitInterval × (stages j).space k ↦ z.2.1) he
    exact midpoint_ne_zero ht.symm

/-- The actual adjacent inclusion track, relative to the false point. -/
def adjacentTrack (k i : ℕ) :
    (((Telescope.inclusion stages step i).map k).comp (ContinuousMap.id Bool)).HomotopyRel
      (((Telescope.inclusion stages step (i + 1)).map k).comp (ContinuousMap.id Bool))
        {false} :=
  (Telescope.inclusionHomotopy stages step i).levelHomotopy k

example (k i : ℕ) : ∃ N, ∃ hi : i ≤ N, ∃ hj : i + 1 ≤ N,
    Nonempty ((((Telescope.transition stages step i N hi).map k).comp
      (ContinuousMap.id Bool)).HomotopyRel
        (((Telescope.transition stages step (i + 1) N hj).map k).comp
          (ContinuousMap.id Bool)) {false}) :=
  Telescope.exists_eventual_homotopy stages step k {false}
    (ContinuousMap.id Bool) (ContinuousMap.id Bool) (adjacentTrack k i)

/-- Both values are admissible zero-dimensional loops: their cube boundary is empty. -/
def boolZeroLoop (b : Bool) : GenLoop (Fin 0) Bool false :=
  ⟨ContinuousMap.const _ b, fun _ ⟨i, _⟩ ↦ Fin.elim0 i⟩

def boolZeroClass (b : Bool) : HomotopyGroup.Pi 0 Bool false :=
  ⟦boolZeroLoop b⟧

lemma boolZeroClass_ne : boolZeroClass false ≠ boolZeroClass true := by
  intro h
  obtain ⟨H⟩ := Quotient.exact h
  have hc : Continuous (fun s : unitInterval ↦ H (s, 0)) := by fun_prop
  have he := TotallyDisconnectedSpace.eq_of_continuous
    (fun s : unitInterval ↦ H (s, 0)) hc 0 1
  rw [H.apply_zero, H.apply_one] at he
  change false = true at he
  cases he

example (k i : ℕ) :
    colimit.ι (Telescope.homotopyDiagram stages step k 0) i ≫
      (Telescope.homotopyColimitIso stages step k 0).hom =
        TypeCat.ofHom (HomotopyGroup.map ((Telescope.inclusion stages step i).map k)
          ((Telescope.inclusion stages step i).map_point k)) :=
  Telescope.homotopyColimitIso_ι_hom stages step k 0 i

lemma included_zero_classes_ne (k i : ℕ) :
    HomotopyGroup.map ((Telescope.inclusion stages step i).map k)
        ((Telescope.inclusion stages step i).map_point k) (boolZeroClass false) ≠
      HomotopyGroup.map ((Telescope.inclusion stages step i).map k)
        ((Telescope.inclusion stages step i).map_point k) (boolZeroClass true) := by
  intro h
  have hp := congrArg (HomotopyGroup.map (projection.map k) (projection.map_point k)) h
  exact boolZeroClass_ne hp

example (k i : ℕ) :
    colimit.ι (Telescope.homotopyDiagram stages step k 0) i (boolZeroClass false) ≠
      colimit.ι (Telescope.homotopyDiagram stages step k 0) i (boolZeroClass true) := by
  intro h
  have hp := congrArg (Telescope.homotopyColimitIso stages step k 0).hom h
  have hi := Telescope.homotopyColimitIso_ι_hom stages step k 0 i
  have hfalse := congrArg (fun g ↦ g (boolZeroClass false)) hi
  have htrue := congrArg (fun g ↦ g (boolZeroClass true)) hi
  exact included_zero_classes_ne k i (hfalse.symm.trans (hp.trans htrue))

section General

variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))

example (N k i : ℕ) (r s t : unitInterval) (x : (E i).space k) :
    Telescope.sweepFamily E f N (k + 1)
        (Telescope.cylinder E f (k + 1) i (r, (E i).structureMap k x t)) s =
      Telescope.structureMap E f k
        (Telescope.sweepFamily E f N k (Telescope.cylinder E f k i (r, x)) s) t :=
  Telescope.sweepFamily_comm E f N k (Telescope.cylinder E f k i (r, x)) s t

example (N k : ℕ) (s : unitInterval) :
    Telescope.sweepFamily E f N k (Telescope.point E f k) s = Telescope.point E f k :=
  Telescope.sweepFamily_point E f N k s

example (N k i : ℕ) (h : N < i) (r s : unitInterval) (x : (E i).space k) :
    Telescope.sweepFamily E f N k (Telescope.cylinder E f k i (r, x)) s =
      Telescope.cylinder E f k i (r, x) :=
  Telescope.sweepPiece_of_gt E f h k (r, x) s

variable [∀ i k, T1Space ((E i).space k)]

example (k n : ℕ)
    (a : HomotopyGroup.Pi n (Telescope.Space E f k) (Telescope.point E f k)) :
    ∃ i, ∃ b : HomotopyGroup.Pi n ((E i).space k) ((E i).point k),
      HomotopyGroup.map ((Telescope.inclusion E f i).map k)
        ((Telescope.inclusion E f i).map_point k) b = a :=
  Telescope.exists_homotopyGroup_representative E f k n a

example (k n : ℕ) {i j : ℕ}
    (a : HomotopyGroup.Pi n ((E i).space k) ((E i).point k))
    (b : HomotopyGroup.Pi n ((E j).space k) ((E j).point k))
    (h : HomotopyGroup.map ((Telescope.inclusion E f i).map k)
        ((Telescope.inclusion E f i).map_point k) a =
      HomotopyGroup.map ((Telescope.inclusion E f j).map k)
        ((Telescope.inclusion E f j).map_point k) b) :
    ∃ N, ∃ hi : i ≤ N, ∃ hj : j ≤ N,
      HomotopyGroup.map ((Telescope.transition E f i N hi).map k)
          ((Telescope.transition E f i N hi).map_point k) a =
        HomotopyGroup.map ((Telescope.transition E f j N hj).map k)
          ((Telescope.transition E f j N hj).map_point k) b :=
  Telescope.exists_eventual_homotopyGroup_eq E f k n a b h

example (d : ℤ) (n : ℕ) (a : (stableSystem (Telescope.prespectrum E f) d).obj n) :
    ∃ i, ∃ b : (stableSystem (E i) d).obj n,
      (stableSystemMap (Telescope.inclusion E f i) d).app n b = a :=
  Telescope.exists_stableStage_representative E f d n a

example (d : ℤ) (a : stableHomotopyGroup (Telescope.prespectrum E f) d) :
    ∃ i, ∃ b : stableHomotopyGroup (E i) d,
      (stableHomotopyFunctor d).map (Telescope.inclusion E f i) b = a :=
  Telescope.exists_stable_representative E f d a

example (d : ℤ) {i j : ℕ} (a : stableHomotopyGroup (E i) d)
    (b : stableHomotopyGroup (E j) d)
    (h : (stableHomotopyFunctor d).map (Telescope.inclusion E f i) a =
      (stableHomotopyFunctor d).map (Telescope.inclusion E f j) b) :
    ∃ N, ∃ hi : i ≤ N, ∃ hj : j ≤ N,
      (stableHomotopyFunctor d).map (Telescope.transition E f i N hi) a =
        (stableHomotopyFunctor d).map (Telescope.transition E f j N hj) b :=
  Telescope.exists_eventual_stable_eq E f d a b h

example (d : ℤ) : IsIso (Telescope.stableColimitComparison E f d) := inferInstance

example (d : ℤ) (i : ℕ) :
    colimit.ι (Telescope.stageStableDiagram E f d) i ≫
      (Telescope.stableColimitIso E f d).hom =
        (stableHomotopyFunctor d).map (Telescope.inclusion E f i) :=
  Telescope.stableColimitIso_ι_hom E f d i

variable (E' : ℕ → LoopPrespectrum.{u}) (f' : ∀ i, E' i ⟶ E' (i + 1))
    (a : ∀ i, E i ⟶ E' i) (ha : ∀ i, a i ≫ f' i = f i ≫ a (i + 1))
    [∀ i k, T1Space ((E' i).space k)]

example (d : ℤ) :
    colimMap (Telescope.stageStableDiagramMap E f E' f' a ha d) ≫
        (Telescope.stableColimitIso E' f' d).hom =
      (Telescope.stableColimitIso E f d).hom ≫
        (stableHomotopyFunctor d).map (Telescope.map E f E' f' a ha) :=
  Telescope.stableColimitIso_naturality E f E' f' a ha d

end General

end ColibTest.PrespectrumTelescopeFiniteStage
