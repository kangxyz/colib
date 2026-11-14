/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.DiagonalTensorTerms
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionRelativeLeray.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.AcyclicityAndBoundedBelow

/-! # Higher direct images of the diagonal quotient with coefficients

For the first projection, a coefficient module pushed forward along the
closed diagonal has no higher direct images, since the composite morphism
is the identity. This does not require the coefficient module to be flat.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.CompositeRightDerived
open Stacks.AlgebraicGeometry.ClosedImmersionRelativeLeray

namespace AlgebraicGeometry.Scheme

universe u

attribute [local instance 2000] HasDerivedCategory.standard

variable (X : Scheme.{u})

local notation "P" => projectiveSpaceOver 1 X
local notation "π" => (P ↘ X)
local notation "Δ" => pullback.diagonal π
local notation "p₁" => pullback.fst π π
local notation "S" => projectiveLineDiagonalSequence X

/-- The higher direct images of the last term in the diagonal coefficient sequence vanish
under the first projection. -/
theorem projectiveLineDiagonalCoefficientLast_isZero_rightDerived
    (E : (P).Modules) (n : ℕ) (hn : 0 < n) :
    IsZero (((Modules.pushforward p₁).rightDerived n).obj
      ((projectiveLineDiagonalCoefficientFunctor X E).obj (S).X₃)) := by
  let := isProper_projectiveSpaceOver 1 X
  have h : IsZero (((Modules.pushforward (Δ ≫ p₁)).rightDerived n).obj E) :=
    (by
      have hId := Stacks.Cohomology.ModuleComparison.rightAcyclic_of_exact (𝟭 (P).Modules) E
      have h0 := (Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat
        (𝟭 (P).Modules) E).1 hId n hn
      exact h0.of_iso ((rightDerivedNatIso
        (Modules.pushforwardCongr (pullback.diagonal_fst π) ≪≫ Modules.pushforwardId P) n).app E))
  exact ((isZero_rightDerived_pushforward_iff Δ p₁ E n).2 h).of_iso
    (((Modules.pushforward p₁).rightDerived n).mapIso
      (projectiveLineDiagonalCoefficientLastIso X E))

end AlgebraicGeometry.Scheme
