/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Morphisms.Finite.Norm.GlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenChartOrderOfVanishing

/-!
# The germ of the same norm ratio in an original affine frame

On an actual open chart the coefficient multiplication identities give a
cross product in the function field of the original affine scheme. The
formula uses the native determinant norm and its exact base change.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Morphisms

universe u

namespace AlgebraicGeometry.Scheme

/-- The regular norm ratio has the cross product of the original sections
as its generic germ in the original affine coordinates. -/
theorem affineNormCrossProduct_of_open {X Y W : Scheme.{u}}
    [IsIntegral Y] [IsIntegral W] [IsAffine Y]
    (f : X ⟶ Y) [IsFiniteLocallyFree f] (i : W ⟶ Y) [IsDominant i]
    (a₁ b₁ : Γ(X, ⊤)) (a₂ b₂ : Γ(Y, ⊤))
    (c₁ : Γ(pullback f i, ⊤)) (c₂ t : Γ(W, ⊤))
    (hc₁ : c₁ * (pullback.fst f i).appTop a₁ = (pullback.fst f i).appTop b₁)
    (hc₂ : c₂ * i.appTop a₂ = i.appTop b₂)
    (r : Y.functionField) :
    letI : Nonempty (⊤ : W.Opens) := ⟨⟨genericPoint W, trivial⟩⟩
    letI : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
    letI : IsFiniteLocallyFree (pullback.snd f i) :=
      isFiniteLocallyFree_isStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback f i) inferInstance
    letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    ∀ [Module.Free Γ(Y, ⊤) Γ(X, ⊤)],
      dominantFunctionFieldMap i r = W.germToFunctionField ⊤ t →
      normTop (pullback.snd f i) c₁ * t = c₂ →
      r * Y.germToFunctionField ⊤ (Algebra.norm Γ(Y, ⊤) b₁) * Y.germToFunctionField ⊤ a₂ =
        Y.germToFunctionField ⊤ (Algebra.norm Γ(Y, ⊤) a₁) * Y.germToFunctionField ⊤ b₂ := by
  dsimp only
  let : Nonempty (⊤ : W.Opens) := ⟨⟨genericPoint W, trivial⟩⟩
  let : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
  let g := pullback.snd f i
  let : IsFiniteLocallyFree g := isFiniteLocallyFree_isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback f i) inferInstance
  let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  intro hfree hr ht
  let : Module.Free Γ(Y, ⊤) Γ(X, ⊤) := hfree
  have hn (s : Γ(X, ⊤)) :
      i.appTop (Algebra.norm Γ(Y, ⊤) s) = normTop g ((pullback.fst f i).appTop s) := by
    rw [← normTop_eq_affineNorm f s]
    exact (normTop_appTop_of_isPullback f g (pullback.fst f i) i
      (IsPullback.of_hasPullback f i) s).symm
  have hnorm : normTop g c₁ * normTop g ((pullback.fst f i).appTop a₁) =
      normTop g ((pullback.fst f i).appTop b₁) := by
    rw [← map_mul, hc₁]
  have hprod : t * i.appTop (Algebra.norm Γ(Y, ⊤) b₁) * i.appTop a₂ =
      i.appTop (Algebra.norm Γ(Y, ⊤) a₁) * i.appTop b₂ := by
    rw [hn b₁, hn a₁, ← hnorm, ← hc₂, ← ht]
    ring
  apply (dominantFunctionFieldMap i).injective
  simp only [map_mul, hr, dominantFunctionFieldMap_germToFunctionField_top]
  simpa only [map_mul] using congrArg (fun s ↦ W.germToFunctionField ⊤ s) hprod

end AlgebraicGeometry.Scheme
