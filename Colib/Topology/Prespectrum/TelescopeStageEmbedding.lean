/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.TelescopeSeparation

/-!
# Original stage embeddings in the reduced telescope

The original stage inclusions are injective. For T1 stages they are closed
embeddings, with incoming endpoint fibers accounted for explicitly. These
statements concern the unchanged quotient topology and original inclusions.
-/
@[expose] public section

open Topology

noncomputable section
open CategoryTheory Set
open scoped unitInterval
open unitInterval
universe u
namespace Topology.LoopPrespectrum.Telescope
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1)) (k : ℕ)

/-- No original stage points are identified by the reduced telescope quotient. -/
theorem inclusion_injective (N : ℕ) : Function.Injective ((inclusion E f N).map k) := by
  classical
  intro x y h
  change Quot.mk (Relation E f k) ⟨N, (0, x)⟩ = Quot.mk _ ⟨N, (0, y)⟩ at h
  rw [quot_eq_iff_normalForm_eq] at h
  simp only [normalForm, zero_ne_one, ↓reduceIte] at h
  split_ifs at h with hx hy
  · exact hx.trans hy.symm
  · have hs := Option.some.inj h
    exact congrArg (fun z : I × (E N).space k ↦ z.2) (eq_of_heq (Sigma.mk.inj hs).2)

/-- The original stage slice, expressed in the disjoint union before quotienting. -/
def stageSlice (N : ℕ) (S : Set ((E N).space k)) : Set (Σ i, I × (E i).space k) :=
  (fun x ↦ ⟨N, (0, x)⟩) '' S

/-- Preimages of stage images retain exactly the lower and incoming upper slices and base fiber. -/
theorem cylinder_mem_stage_image_iff (N i : ℕ) (S : Set ((E N).space k))
    (z : I × (E i).space k) :
    cylinder E f k i z ∈ ((inclusion E f N).map k) '' S ↔
      ((E N).point k ∈ S ∧ cylinder E f k i z = point E f k) ∨
      (⟨i, z⟩ : Σ j, I × (E j).space k) ∈ stageSlice E k N S ∨
      z.1 = 1 ∧
        (⟨i + 1, (0, (f i).map k z.2)⟩ : Σ j, I × (E j).space k) ∈
          stageSlice E k N S := by
  classical
  constructor
  · rintro ⟨y, hy, heq⟩
    by_cases hyp : y = (E N).point k
    · subst y
      exact Or.inl ⟨hy, heq.symm.trans ((inclusion E f N).map_point k)⟩
    · have hn : normalForm E f k ⟨i, z⟩ = some ⟨N, (0, y)⟩ := by
        have h := (quot_eq_iff_normalForm_eq E f k ⟨i, z⟩ ⟨N, (0, y)⟩).mp heq.symm
        simpa only [normalForm, zero_ne_one, ↓reduceIte, hyp] using h
      rcases (normalForm_eq_some_iff E f k i z ⟨N, (0, y)⟩ ⟨zero_ne_one, hyp⟩).mp hn with
        h | ⟨ht, h⟩
      · exact Or.inr (Or.inl ⟨y, hy, h.symm⟩)
      · exact Or.inr (Or.inr ⟨ht, y, hy, h.symm⟩)
  · rintro (⟨hp, h⟩ | h | ⟨ht, h⟩)
    · exact ⟨(E N).point k, hp, ((inclusion E f N).map_point k).trans h.symm⟩
    · obtain ⟨y, hy, h⟩ := h
      exact ⟨y, hy, congrArg (Quot.mk (Relation E f k)) h⟩
    · obtain ⟨y, hy, h⟩ := h
      refine ⟨y, hy, ?_⟩
      change Quot.mk (Relation E f k) ⟨N, (0, y)⟩ = _
      change (⟨N, (0, y)⟩ : Σ j, I × (E j).space k) = _ at h
      rw [h]
      exact (cylinder_one E f k i z.2).symm.trans
        (congrArg (cylinder E f k i) (Prod.ext ht.symm rfl))

/-- A closed original stage subset gives a closed slice before quotienting. -/
theorem isClosed_stageSlice (N : ℕ) {S : Set ((E N).space k)} (hS : IsClosed S) :
    IsClosed (stageSlice E k N S) := by
  have h : IsClosed ((Sigma.mk N) '' ({0} ×ˢ S) : Set (Σ i, I × (E i).space k)) :=
    @isClosedMap_sigmaMk ℕ (fun i ↦ I × (E i).space k) (fun _ ↦ inferInstance) N _
      (isClosed_singleton.prod hS)
  convert h using 1
  ext z
  simp only [stageSlice, mem_image, mem_prod, mem_singleton_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(0, x), ⟨rfl, hx⟩, rfl⟩
  · rintro ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
    change t = 0 at ht
    subst t
    exact ⟨x, hx, rfl⟩

variable [∀ i, T1Space ((E i).space k)]

/-- The unchanged original stage inclusion is a closed map. -/
theorem isClosedMap_inclusion (N : ℕ) : IsClosedMap ((inclusion E f N).map k) := by
  intro S hS
  apply isQuotientMap_quot_mk.isClosed_preimage.mp
  apply isClosed_sigma_iff.mpr
  intro i
  change IsClosed {z : I × (E i).space k |
    cylinder E f k i z ∈ ((inclusion E f N).map k) '' S}
  simp_rw [cylinder_mem_stage_image_iff]
  have hbase : IsClosed {z : I × (E i).space k |
      (E N).point k ∈ S ∧ cylinder E f k i z = point E f k} :=
    isClosed_const.inter (isClosed_cylinder_fiber E f k i (point E f k))
  have hstart : IsClosed {z : I × (E i).space k |
      (⟨i, z⟩ : Σ j, I × (E j).space k) ∈ stageSlice E k N S} :=
    (isClosed_stageSlice E k N hS).preimage (continuous_sigmaMk (i := i))
  have hfinish : IsClosed {z : I × (E i).space k |
      (⟨i + 1, (0, (f i).map k z.2)⟩ : Σ j, I × (E j).space k) ∈
        stageSlice E k N S} :=
    (isClosed_stageSlice E k N hS).preimage ((continuous_sigmaMk (i := i + 1)).comp
      (continuous_const.prodMk (((f i).map k).continuous.comp continuous_snd)))
  exact hbase.union (hstart.union ((isClosed_singleton.preimage continuous_fst).inter hfinish))

/-- Every original stage is a closed embedded subspace of the actual reduced quotient. -/
theorem isClosedEmbedding_inclusion (N : ℕ) : IsClosedEmbedding ((inclusion E f N).map k) :=
  .of_continuous_injective_isClosedMap ((inclusion E f N).map k).continuous
    (inclusion_injective E f k N) (isClosedMap_inclusion E f k N)

end Topology.LoopPrespectrum.Telescope
