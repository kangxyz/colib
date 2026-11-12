/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Sheafification.Image

/-!
# Detecting an action on the unit image by the original open cover

The unit image is Nisnevich separated, so actions out of one smooth object
can be compared after restriction to an open family covering that object.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme

universe u v

namespace AlgebraicGeometry.PresheafWithTransfers

/-- If the original transfer vanishes on a family of open restrictions
covering its source, its action on the Nisnevich unit image vanishes. -/
theorem nisnevichImage_transfer_eq_zero_of_open_cover
    {k : Type u} [Field k] (P : PresheafWithTransfers.{u + 1} k)
    {X Y : SmoothSite (Spec (.of k))} {ι : Type v}
    (U : ι → SmoothSite (Spec (.of k))) (a : ∀ i, U i ⟶ X)
    [∀ i, IsOpenImmersion (a i).left]
    (hcover : ∀ x : X.left, ∃ (i : ι) (y : (U i).left), (a i).left y = x)
    (δ : Cor.mk X ⟶ Cor.mk Y)
    (hδ : ∀ i, (nisnevichImage P).transfer ((Cor.graphFunctor k).map (a i) ≫ δ) = 0) :
    (nisnevichImage P).transfer δ = 0 := by
  apply ConcreteCategory.hom_ext
  intro s
  let Q := nisnevichImage P
  let F := (toPresheaf k).obj Q
  let t : Q.sections (Cor.mk X) := Q.transfer δ s
  change t = 0
  have hpre : Presieve.ofArrows U a ∈ SmoothSite.nisnevichPrecoverage (Spec (.of k)) X := by
    apply (SmoothSite.ofArrows_mem_nisnevichPrecoverage_iff a).2
    refine ⟨fun i ↦ inferInstance, fun x ↦ ?_⟩
    obtain ⟨i, y, hy⟩ := hcover x
    exact ⟨i, y, hy, inferInstance⟩
  have hsieve : Presheaf.equalizerSieve (F := F) t 0 ∈
      SmoothSite.nisnevichTopology (Spec (.of k)) X := by
    apply SmoothSite.mem_nisnevichTopology_iff.mpr
    refine ⟨Presieve.ofArrows U a, hpre, ?_⟩
    rw [Presieve.ofArrows_le_iff]
    intro i
    let α : Cor.mk (U i) ⟶ Cor.mk X := (Cor.graphFunctor k).map (a i)
    change Q.transfer α (Q.transfer δ s) = Q.transfer α 0
    have hz : Q.transfer (α ≫ δ) = 0 := hδ i
    calc
      _ = Q.transfer (α ≫ δ) s := by rw [transfer_comp]; rfl
      _ = _ := by rw [hz]; simp
  exact nisnevichImage_isSeparated P X _ hsieve t 0 (fun _ _ hf ↦ hf)

end AlgebraicGeometry.PresheafWithTransfers
