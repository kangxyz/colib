/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Morphisms.Finite.Marked.Norm
public import Colib.AlgebraicGeometry.Morphisms.Finite.Norm.AffineBaseChange

/-!
# Boundary values of a norm association unit

The same norm association unit is one on a full inverse boundary with
unit coefficients and on a full marked boundary with an unchanged regular
coefficient. The second assertion uses the actual residual scheme.

Adapted from
`Motivic/Aglib/AlgebraicGeometry/RelativeCurve/Pencils/Boundary/SectionPairNormUnit.lean`
at a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {W Z T : Scheme.{u}} [IsAffine W] [IsAffine Z]
  (p : T ⟶ W) [IsFinite p] (z : Z ⟶ W)

/-- The association unit restricts to one when both original coefficients
restrict to one on the full inverse boundary and on the target boundary. -/
theorem appTop_normAssociationUnit_eq_one_of_inverseBoundary
    (b : Γ(T, ⊤)) (a : Γ(W, ⊤)) (μ : Γ(W, ⊤)ˣ)
    (hb : (pullback.fst p z).appTop b = 1) (ha : z.appTop a = 1) :
    let : Algebra Γ(W, ⊤) Γ(T, ⊤) := p.appTop.hom.toAlgebra
    ∀ [Module.Free Γ(W, ⊤) Γ(T, ⊤)],
      Algebra.norm Γ(W, ⊤) b = (μ : Γ(W, ⊤)) * a → z.appTop (μ : Γ(W, ⊤)) = 1 := by
  dsimp only
  let : Algebra Γ(W, ⊤) Γ(T, ⊤) := p.appTop.hom.toAlgebra
  let : Algebra Γ(Z, ⊤) Γ(pullback p z, ⊤) := (pullback.snd p z).appTop.hom.toAlgebra
  intro hfree hμ
  let : Module.Free Γ(W, ⊤) Γ(T, ⊤) := hfree
  have hn := affineNorm_appTop_of_isPullback p z (pullback.fst p z) (pullback.snd p z)
    (IsPullback.of_hasPullback p z) b
  rw [hμ, map_mul, ha, mul_one, hb, map_one] at hn
  exact hn

/-- On the full marked boundary, cancellation of its actual regular
coordinate computes the restriction of the same association unit. -/
theorem appTop_normAssociationUnit_eq_one_of_markedBoundary
    {Y : Scheme.{u}} (j : Y ⟶ T) [IsOpenImmersion j] (s : Z ⟶ Y)
    (hs : (s ≫ j) ≫ p = z) (H : IsPullback s (𝟙 Z) (j ≫ p) z)
    (b : Γ(T, ⊤)) (a : Γ(W, ⊤)) (μ : Γ(W, ⊤)ˣ)
    (hmarked : (s ≫ j).appTop b = z.appTop a)
    (hresidual : (residualMarkedFiberMap p j z s hs).appTop b = 1)
    (hreg : IsRightRegular (z.appTop a)) :
    let : Algebra Γ(W, ⊤) Γ(T, ⊤) := p.appTop.hom.toAlgebra
    ∀ [Module.Free Γ(W, ⊤) Γ(T, ⊤)],
      Algebra.norm Γ(W, ⊤) b = (μ : Γ(W, ⊤)) * a → z.appTop (μ : Γ(W, ⊤)) = 1 := by
  dsimp only
  let : Algebra Γ(W, ⊤) Γ(T, ⊤) := p.appTop.hom.toAlgebra
  intro hfree hμ
  let : Module.Free Γ(W, ⊤) Γ(T, ⊤) := hfree
  have hn := affineNorm_eq_marked_value p j z s hs H b hresidual
  rw [hμ, map_mul, hmarked] at hn
  exact hreg (hn.trans (one_mul (z.appTop a)).symm)

end AlgebraicGeometry.Scheme
