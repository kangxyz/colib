/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.DiagonalTensorTerms
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensor

/-! # Naturality of the quotient in the projective-line diagonal resolution

The last term is the diagonal direct image of the coefficient, naturally in
that coefficient. The ordinary first projection of the term is the identity.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Prod

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u})

local notation "P" => projectiveSpaceOver 1 X
local notation "π" => (P ↘ X)
local notation "Q" => pullback π π
local notation "Δ" => pullback.diagonal π
local notation "p₁" => pullback.fst π π
local notation "p₂" => pullback.snd π π
local notation "S" => projectiveLineDiagonalSequence X

local notation "O" Z => _root_.SheafOfModules.unit (Scheme.ringCatSheaf Z)
local notation "T" Z => Stacks.SheafOfModules.Tensor.sheafTensor (Scheme.sheaf Z)

set_option backward.isDefEq.respectTransparency false

/-- The left unit law as a natural isomorphism for the native sheaf tensor. -/
def diagonalUnitTensorNatIso (Z : Scheme.{u}) :
    (T Z).obj (O Z) ≅ 𝟭 Z.Modules := by
  let : MonoidalCategory Z.Modules := SheafOfModules.monoidalCategorySheafTensor Z.sheaf
  change tensorLeft (𝟙_ Z.Modules) ≅ 𝟭 Z.Modules
  exact leftUnitorNatIso Z.Modules

/-- The closed-immersion projection formula in the variable coefficient. -/
def projectiveLineDiagonalQuotientProjectionFormula :
    (T Q).obj (S).X₃ ≅
      (Modules.pullback Δ ⋙ (T P).obj (O P)) ⋙ Modules.pushforward Δ := by
  let := isProper_projectiveSpaceOver 1 X
  refine NatIso.ofComponents
    (Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso Δ (O P)) ?_
  intro A B f
  have hn := Stacks.AffineProjectionFormula.projectionFormulaMap_natural
    (Δ).toLRSHom.toShHom (𝟙 (O P)) f
  let i := (Δ).toLRSHom.toShHom
  let A₀ := (Modules.pushforward Δ).obj (O P)
  let a := (Modules.pullback Δ).obj A
  let b := (Modules.pullback Δ).map f
  have h₁ : (T Q).map ((Modules.pushforward Δ).map (𝟙 (O P))) =
      𝟙 ((T Q).obj A₀) := by
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  have h₂ : (T P).map (𝟙 (O P)) = 𝟙 ((T P).obj (O P)) :=
    CategoryTheory.Functor.map_id _ _
  change (((T Q).map ((Modules.pushforward Δ).map (𝟙 (O P)))).app A ≫
      ((T Q).obj A₀).map f) ≫
      Stacks.AffineProjectionFormula.projectionFormulaMap i (O P) B =
    Stacks.AffineProjectionFormula.projectionFormulaMap i (O P) A ≫
      (Modules.pushforward Δ).map (((T P).map (𝟙 (O P))).app a ≫
        ((T P).obj (O P)).map b) at hn
  rw [h₁, h₂] at hn
  simp only [NatTrans.id_app] at hn
  erw [Category.id_comp, Category.id_comp] at hn
  change ((T Q).obj A₀).map f ≫
      Stacks.AffineProjectionFormula.projectionFormulaMap i (O P) B =
    Stacks.AffineProjectionFormula.projectionFormulaMap i (O P) A ≫
      (Modules.pushforward Δ).map (((T P).obj (O P)).map b)
  exact hn

/-- The actual last term after tensoring with the coefficient pulled back from
the second factor is its diagonal direct image, naturally in the coefficient. -/
def projectiveLineDiagonalCoefficientLastNatIso :
    (Modules.pullback p₂ ⋙ (T Q).obj (S).X₃) ≅ Modules.pushforward Δ :=
  Functor.isoWhiskerLeft (Modules.pullback p₂)
    (projectiveLineDiagonalQuotientProjectionFormula X) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Modules.pullbackComp Δ p₂ ≪≫ Modules.pullbackCongr (pullback.diagonal_snd π) ≪≫
          Modules.pullbackId P) _ ≪≫
      Functor.leftUnitor _ ≪≫ diagonalUnitTensorNatIso P) _ ≪≫
    Functor.leftUnitor _

/-- The canonical ordinary first projection of the last term is the identity functor. -/
def projectiveLineDiagonalCoefficientLastPushforwardNatIso :
    (Modules.pullback p₂ ⋙ (T Q).obj (S).X₃) ⋙ Modules.pushforward p₁ ≅
      𝟭 (P).Modules :=
  Functor.isoWhiskerRight (projectiveLineDiagonalCoefficientLastNatIso X) _ ≪≫
    Modules.pushforwardComp Δ p₁ ≪≫ Modules.pushforwardCongr (pullback.diagonal_fst π) ≪≫
    Modules.pushforwardId P

end AlgebraicGeometry.Scheme
