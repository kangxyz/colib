/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.TelescopeCompactness
public import Colib.Topology.Prespectrum.TelescopeStageEmbedding
public import Colib.Topology.Prespectrum.TelescopeContraction

/-!
# Finite-stage representability in the original reduced telescope

For T1 stages, a map from a compact pair to the original reduced telescope is
based-homotopic into an original stage. The proof combines bounded cylinder
support, an actual finite-prefix contraction and the closed embedding of the
unchanged stage inclusion. The same contraction handles entire compact-domain
homotopies and retains their original stage endpoint maps.
-/
@[expose] public section

open Topology


noncomputable section
open CategoryTheory Set Topology
open scoped unitInterval
open unitInterval
universe u v
namespace Topology.LoopPrespectrum.Telescope
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1)) (k : ℕ)
  [∀ i, T1Space ((E i).space k)]

/-- Continuous factorization through an original stage, when the range lies in that stage. -/
def liftStage {A : Type v} [TopologicalSpace A] (N : ℕ) (g : C(A, Space E f k))
    (hg : ∀ a, g a ∈ range ((inclusion E f N).map k)) : C(A, (E N).space k) where
  toFun a := Classical.choose (hg a)
  continuous_toFun := by
    apply (isClosedEmbedding_inclusion E f k N).isEmbedding.isInducing.continuous_iff.mpr
    have h : (fun a ↦ (inclusion E f N).map k (Classical.choose (hg a))) = g :=
      funext (fun a ↦ Classical.choose_spec (hg a))
    change Continuous (fun a ↦ (inclusion E f N).map k (Classical.choose (hg a)))
    rw [h]
    exact g.continuous

@[simp] theorem inclusion_liftStage {A : Type v} [TopologicalSpace A] (N : ℕ)
    (g : C(A, Space E f k)) (hg : ∀ a, g a ∈ range ((inclusion E f N).map k)) (a : A) :
    (inclusion E f N).map k (liftStage E f k N g hg a) = g a :=
  Classical.choose_spec (hg a)

omit [∀ i, T1Space ((E i).space k)] in
/-- A bound on original cylinder support puts the collapsed map in the original later stage. -/
theorem collapse_mem_stage {A : Type v} [TopologicalSpace A] (g : C(A, Space E f k))
    {B N : ℕ} (hBN : B < N)
    (hg : ∀ a, ∃ i ≤ B, ∃ z, cylinder E f k i z = g a) (a : A) :
    (collapse E f N).map k (g a) ∈ range ((inclusion E f N).map k) := by
  obtain ⟨i, hi, z, hz⟩ := hg a
  rw [← hz, collapse_cylinder_of_lt E f (hi.trans_lt hBN)]
  exact mem_range_self _

/-- Every compact relative based map is homotopic to an actual original-stage map. -/
theorem exists_stage_representative {A : Type v} [TopologicalSpace A] [CompactSpace A]
    (S : Set A) (g : C(A, Space E f k)) (hg : ∀ a ∈ S, g a = point E f k) :
    ∃ N : ℕ, ∃ p : C(A, (E N).space k),
      (∀ a ∈ S, p a = (E N).point k) ∧
      Nonempty (g.HomotopyRel (((inclusion E f N).map k).comp p) S) := by
  obtain ⟨B, hB⟩ := exists_cylinder_bound E f k g
  let c := ((collapse E f (B + 1)).map k).comp g
  have hc (a : A) : c a ∈ range ((inclusion E f (B + 1)).map k) :=
    collapse_mem_stage E f k g (Nat.lt_succ_self B) hB a
  let p := liftStage E f k (B + 1) c hc
  have hp (a : A) : (inclusion E f (B + 1)).map k (p a) = c a :=
    inclusion_liftStage E f k (B + 1) c hc a
  refine ⟨B + 1, p, ?_, ⟨?_⟩⟩
  · intro a ha
    apply inclusion_injective E f k (B + 1)
    rw [hp, (inclusion E f (B + 1)).map_point]
    change (collapse E f (B + 1)).map k (g a) = _
    rw [hg a ha]
    exact (collapse E f (B + 1)).map_point k
  · exact
      { toFun := fun z ↦ (collapseHomotopy E f (B + 1)).level k (z.1, g z.2)
        continuous_toFun := ((collapseHomotopy E f (B + 1)).level k).continuous.comp
          (continuous_fst.prodMk (g.continuous.comp continuous_snd))
        map_zero_left := fun a ↦ (collapseHomotopy E f (B + 1)).at_zero k (g a)
        map_one_left := fun a ↦
          ((collapseHomotopy E f (B + 1)).at_one k (g a)).trans
            (hp a).symm
        prop' := fun t a ha ↦ by
          change (collapseHomotopy E f (B + 1)).level k (t, g a) = g a
          rw [hg a ha]
          exact (collapseHomotopy E f (B + 1)).at_point k t }

/-- Every original based sphere map comes from an original stage up to based homotopy. -/
theorem exists_genLoop_representative (n : ℕ)
    (p : GenLoop (Fin n) (Space E f k) (point E f k)) :
    ∃ N : ℕ, ∃ q : GenLoop (Fin n) ((E N).space k) ((E N).point k),
      GenLoop.Homotopic p
        (GenLoop.postcomp ((inclusion E f N).map k) ((inclusion E f N).map_point k) q) := by
  obtain ⟨N, q, hq, H⟩ := exists_stage_representative E f k (Cube.boundary (Fin n)) p.val p.property
  exact ⟨N, ⟨q, hq⟩, H⟩

/-- The original telescope homotopy group is covered by the actual stage homotopy maps. -/
theorem exists_homotopyGroup_representative (n : ℕ)
    (a : HomotopyGroup.Pi n (Space E f k) (point E f k)) :
    ∃ N : ℕ, ∃ b : HomotopyGroup.Pi n ((E N).space k) ((E N).point k),
      HomotopyGroup.map ((inclusion E f N).map k) ((inclusion E f N).map_point k) b = a := by
  induction a using Quotient.inductionOn with
  | h p =>
    obtain ⟨N, q, H⟩ := exists_genLoop_representative E f k n p
    exact ⟨N, Quotient.mk' q, (Quotient.sound H).symm⟩

end Topology.LoopPrespectrum.Telescope
