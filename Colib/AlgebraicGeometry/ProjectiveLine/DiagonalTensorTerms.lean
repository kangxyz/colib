/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.DiagonalIdealLine
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorRightUnit

/-! # The coefficient terms in the diagonal resolution

Pulling a module back from the second factor and tensoring the diagonal
quotient with it gives its direct image along the diagonal. The first
projection then recovers the original coefficient module.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.RelativeVeryAmple
set_option backward.isDefEq.respectTransparency false

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

/-- Tensor on the right by the pullback of a coefficient module from the second factor. -/
abbrev projectiveLineDiagonalCoefficientFunctor (E : (P).Modules) :
    (Q).Modules ⥤ (Q).Modules :=
  (Stacks.SheafOfModules.Tensor.sheafTensor (Q).sheaf).flip.obj ((Modules.pullback p₂).obj E)

/-- The first term of the diagonal resolution after tensoring with coefficients. -/
def projectiveLineDiagonalCoefficientFirstIso (E : (P).Modules) :
    tensorModules Q (projectiveLineDiagonalNegativeTwist X) ((Modules.pullback p₂).obj E) ≅
      (projectiveLineDiagonalCoefficientFunctor X E).obj (S).X₁ :=
  (projectiveLineDiagonalCoefficientFunctor X E).mapIso (projectiveLineDiagonalSequenceFirstIso X)

/-- The middle term of the diagonal resolution after tensoring with coefficients. -/
def projectiveLineDiagonalCoefficientMiddleIso (E : (P).Modules) :
    (projectiveLineDiagonalCoefficientFunctor X E).obj (S).X₂ ≅
      (Modules.pullback p₂).obj E :=
  Stacks.unitSheafTensorIso (O := (Q).sheaf) _

/-- The last term is the diagonal direct image of the coefficient module. -/
def projectiveLineDiagonalCoefficientLastIso (E : (P).Modules) :
    (projectiveLineDiagonalCoefficientFunctor X E).obj (S).X₃ ≅
      (Modules.pushforward Δ).obj E := by
  let := isProper_projectiveSpaceOver 1 X
  let F := (Modules.pullback p₂).obj E
  let e : (Modules.pullback Δ).obj F ≅ E :=
    ((Modules.pullbackComp Δ p₂) ≪≫ Modules.pullbackCongr (pullback.diagonal_snd π) ≪≫
      Modules.pullbackId P).app E
  exact Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso Δ
      (_root_.SheafOfModules.unit (P).ringCatSheaf) F ≪≫
    (Modules.pushforward Δ).mapIso (Stacks.unitSheafTensorIso (O := (P).sheaf) _ ≪≫ e)

/-- The first projection sends the last term of the coefficient diagonal sequence to the
coefficient module. -/
def projectiveLineDiagonalCoefficientLastPushforwardIso (E : (P).Modules) :
    (Modules.pushforward p₁).obj
      ((projectiveLineDiagonalCoefficientFunctor X E).obj (S).X₃) ≅ E :=
  (Modules.pushforward p₁).mapIso (projectiveLineDiagonalCoefficientLastIso X E) ≪≫
    (Modules.pushforwardComp Δ p₁ ≪≫
      Modules.pushforwardCongr (pullback.diagonal_fst π) ≪≫ Modules.pushforwardId P).app E

end AlgebraicGeometry.Scheme
