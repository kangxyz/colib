/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.Convolution
import Colib.AlgebraicGeometry.Correspondences.Coproducts.Binary

/-!
# Linearity of convolution cocones in the correspondence label

A family of bilinear coefficient pairings satisfying the transfer relations
is additive in the correspondence label. The proof uses the two projections
and the fold of the original binary biproduct in the correspondence category.
This is the extra relation needed to identify the integral coend with
ordinary pointwise Day convolution on the additive coefficient functors.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

local notation "PST(" K ")" => TransferCoefficients K

variable (F : Cor k ⥤ Cor k ⥤ Cor k) [F.Additive]
variable {P Q : PST(k)} {X : Cor k} {M : Type v} [AddCommGroup M]

/-- The two transfer relations already force addition in the correspondence label. -/
theorem convolutionPairing_add_correspondence
    (e : ∀ Y Z : Cor k, (X ⟶ (F.obj Y).obj Z) → (sections P Y →+ sections Q Z →+ M))
    (he : ∀ {Y Y' Z Z' : Cor k} (f : Y ⟶ Y') (g : Z ⟶ Z')
      (s : sections P Y') (t : sections Q Z') (a : X ⟶ (F.obj Y).obj Z),
      e Y Z a (transfer P f s) (transfer Q g t) =
        e Y' Z' (a ≫ convolutionCorrespondenceMap F f g) s t)
    (Y Z : Cor k) (a b : X ⟶ (F.obj Y).obj Z) (s : sections P Y) (t : sections Q Z) :
    e Y Z (a + b) s t = e Y Z a s t + e Y Z b s t := by
  let G := F.flip.obj Z
  let p₁ : (Y ⊞ Y) ⟶ Y := biprod.fst
  let p₂ : (Y ⊞ Y) ⟶ Y := biprod.snd
  let i₁ : Y ⟶ (Y ⊞ Y) := biprod.inl
  let i₂ : Y ⟶ (Y ⊞ Y) := biprod.inr
  let d : X ⟶ G.obj (Y ⊞ Y) := a ≫ G.map i₁ + b ≫ G.map i₂
  let : G.Additive :=
    { map_add := by
        intro A B f g
        change (F.map (f + g)).app Z = (F.map f).app Z + (F.map g).app Z
        exact NatTrans.congr_app (F.map_add (f := f) (g := g)) Z }
  have hp₁ : d ≫ G.map p₁ = a := by
    dsimp only [d]
    rw [Preadditive.add_comp, Category.assoc, Category.assoc, ← G.map_comp, ← G.map_comp]
    simp only [i₁, i₂, p₁, biprod.inl_fst, biprod.inr_fst, G.map_id, G.map_zero,
      comp_zero, add_zero]
    exact Category.comp_id a
  have hp₂ : d ≫ G.map p₂ = b := by
    dsimp only [d]
    rw [Preadditive.add_comp, Category.assoc, Category.assoc, ← G.map_comp, ← G.map_comp]
    simp only [i₁, i₂, p₂, biprod.inl_snd, biprod.inr_snd, G.map_id, G.map_zero,
      comp_zero, zero_add]
    exact Category.comp_id b
  have hp : d ≫ G.map (p₁ + p₂) = a + b := by
    rw [G.map_add, Preadditive.comp_add, hp₁, hp₂]
  have h (f : (Y ⊞ Y) ⟶ Y) :
      e (Y ⊞ Y) Z d (transfer P f s) t = e Y Z (d ≫ G.map f) s t := by
    have hf := he f (𝟙 Z) s t d
    change e (Y ⊞ Y) Z d (transfer P f s) (transfer Q (𝟙 Z) t) =
      e Y Z (d ≫ ((F.map f).app Z ≫ (F.obj Y).map (𝟙 Z))) s t at hf
    have hmap : (F.obj Y).map (𝟙 Z) = 𝟙 ((F.obj Y).obj Z) := (F.obj Y).map_id Z
    rw [hmap, Category.comp_id] at hf
    have ht : transfer Q (𝟙 Z) t = t := (ConcreteCategory.congr_hom (transfer_id Q Z) t)
    have h' := congrArg (fun z : sections Q Z => e (Y ⊞ Y) Z d (transfer P f s) z) ht
    change e (Y ⊞ Y) Z d (transfer P f s) t =
      e Y Z (d ≫ (F.map f).app Z) s t
    exact h'.symm.trans hf
  rw [← hp, ← h, transfer_add]
  change e (Y ⊞ Y) Z d (transfer P p₁ s + transfer P p₂ s) t = _
  rw [map_add]
  change e (Y ⊞ Y) Z d (transfer P p₁ s) t + e (Y ⊞ Y) Z d (transfer P p₂ s) t = _
  rw [h p₁, h p₂, hp₁, hp₂]

end AlgebraicGeometry.PresheafWithTransfers
