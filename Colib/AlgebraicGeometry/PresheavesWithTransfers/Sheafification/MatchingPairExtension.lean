/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Basic

/-!
# Conditional extension of matching transfer sections

Four simultaneous relations between actual signed correspondence actions
extend a matching pair to the target diagram. The middle-degree correction
keeps the original minus sign.

Adapted from Motivic at a6805c4a87cdfd7717dd7a94039246a167f15380,
Motivic/Transfers/Presheaf/Sheafification/MatchingPairExtension.lean.
-/

@[expose] public noncomputable section

open CategoryTheory

universe v u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

/-- The first correspondence extends the matching pair when the same three
correspondences satisfy the four specified action relations. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Transfers/Presheaf/Sheafification/MatchingPairExtension.lean:36-66"
  "adaptation" "Actual transfer action identities and the original correction sign"]
theorem transfer_matchingPair_extension (P : PresheafWithTransfers.{v} k)
    {A Y B X' A' Y' : Cor k}
    (g : B ⟶ A) (u : B ⟶ Y) (i' : A' ⟶ X') (f' : Y' ⟶ X')
    (rA : A' ⟶ A) (rY : Y' ⟶ Y)
    (lambdaA : X' ⟶ A) (lambdaB : Y' ⟶ B) (ψ : A' ⟶ B)
    (hBu : transfer P (lambdaB ≫ u) = transfer P rY)
    (hBg : transfer P (lambdaB ≫ g) = transfer P (f' ≫ lambdaA))
    (hψu : transfer P (ψ ≫ u) = 0)
    (hA : transfer P (i' ≫ lambdaA - ψ ≫ g) = transfer P rA)
    (a : sections P A) (y : sections P Y)
    (hmatch : transfer P g a = transfer P u y) :
    transfer P i' (transfer P lambdaA a) = transfer P rA a ∧
      transfer P f' (transfer P lambdaA a) = transfer P rY y := by
  have hzero := ConcreteCategory.congr_hom hψu y
  rw [transfer_comp, ConcreteCategory.comp_apply] at hzero
  change transfer P ψ (transfer P u y) = 0 at hzero
  have hleft := ConcreteCategory.congr_hom hA a
  rw [transfer_sub, transfer_comp, transfer_comp] at hleft
  change transfer P i' (transfer P lambdaA a) - transfer P ψ (transfer P g a) =
    transfer P rA a at hleft
  rw [hmatch, hzero, sub_zero] at hleft
  refine ⟨hleft, ?_⟩
  have hright := ConcreteCategory.congr_hom hBg a
  simp only [transfer_comp, ConcreteCategory.comp_apply] at hright
  have hrestrict := ConcreteCategory.congr_hom hBu y
  simp only [transfer_comp, ConcreteCategory.comp_apply] at hrestrict
  calc
    transfer P f' (transfer P lambdaA a) = transfer P lambdaB (transfer P g a) := hright.symm
    _ = transfer P lambdaB (transfer P u y) := congrArg (transfer P lambdaB) hmatch
    _ = transfer P rY y := hrestrict

end AlgebraicGeometry.PresheafWithTransfers
