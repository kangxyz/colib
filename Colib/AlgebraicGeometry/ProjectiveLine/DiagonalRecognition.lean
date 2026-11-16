/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.DiagonalDeterminant
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Tactic.FinCases
public import StacksFrontier.AlgebraicGeometry.PullbackTensorIso.Sections
public import StacksFrontier.AlgebraicGeometry.SectionProduct.Tensor

/-! # The projective-line diagonal via cross-multiplication

The determinant vanishes after pullback if and only if the two maps represented by the
ordered coordinate pairs agree. This uses the native projective-space moduli theorem rather
than a pointwise equality on the underlying topological spaces.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.ProjectiveSpaceModuli

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u})

local notation "P" => projectiveSpaceOver 1 X
local notation "π" => (P ↘ X)
local notation "Q" => pullback π π
local notation "τ" => projectiveSpaceOver.toIntegralAtUniverse 1 X
local notation "p₁" => pullback.fst π π
local notation "p₂" => pullback.snd π π

private theorem crossMultiplies_iff_determinant_eq {T : Scheme.{u}}
    (A B : GeneratingTuple T 1) :
    CrossMultiplies A.coord B.coord ↔
      Stacks.SheafOfModules.tensorSectionsAt T.sheaf.obj T.ringCatSheaf.property (op ⊤)
          A.bundle B.bundle (A.coord 0) (B.coord 1) =
        Stacks.SheafOfModules.tensorSectionsAt T.sheaf.obj T.ringCatSheaf.property (op ⊤)
          A.bundle B.bundle (A.coord 1) (B.coord 0) := by
  constructor
  · intro h
    let M := Modules.tensorObj A.bundle B.bundle
    refine TopCat.Presheaf.section_ext ⟨M.presheaf, M.isSheaf⟩ ⊤ _ _ fun x hx => ?_
    apply (tensorStalkEquiv A.bundle B.bundle x).injective
    rw [Stacks.SectionProduct.tensorStalkEquiv_germ_tensorSectionsAt,
      Stacks.SectionProduct.tensorStalkEquiv_germ_tensorSectionsAt]
    exact h x 0 1
  · intro h
    apply crossMultiplies_of_tensorSectionsAt
    intro i j
    fin_cases i <;> fin_cases j
    · rfl
    · exact h
    · exact h.symm
    · rfl

/-- A test morphism kills the diagonal determinant exactly when its two projections agree. -/
theorem projectiveLineDiagonalDeterminant_pullback_eq_zero_iff_projections {T : Scheme.{u}}
    (g : T ⟶ Q) :
    pullbackGlobalSections g (projectiveLineDiagonalPositiveTwist X)
        (projectiveLineDiagonalDeterminant X) = 0 ↔ g ≫ p₁ = g ≫ p₂ := by
  let A := projectiveLineFirstTuple X
  let B := projectiveLineSecondTuple X
  let A' := pullbackTuple g A
  let B' := pullbackTuple g B
  let e := Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso g A.bundle B.bundle
  let eTop := (_root_.SheafOfModules.evaluation (R := T.ringCatSheaf) (op ⊤)).mapIso e
  let φ := eTop.hom
  have hφ : IsIso φ := eTop.isIso_hom
  have hinj := (ConcreteCategory.bijective_of_isIso φ).1
  have h₁₂ : φ
      (pullbackGlobalSections g (projectiveLineDiagonalPositiveTwist X)
        (projectiveLineCoordinateTensor X 0 1)) =
    Stacks.SheafOfModules.tensorSectionsAt T.sheaf.obj T.ringCatSheaf.property (op ⊤)
      A'.bundle B'.bundle (A'.coord 0) (B'.coord 1) :=
    Stacks.PullbackTensorIso.pullbackGlobalSections_tensorSectionsAt g _ _ _ _
  have h₂₁ : φ
      (pullbackGlobalSections g (projectiveLineDiagonalPositiveTwist X)
        (projectiveLineCoordinateTensor X 1 0)) =
    Stacks.SheafOfModules.tensorSectionsAt T.sheaf.obj T.ringCatSheaf.property (op ⊤)
      A'.bundle B'.bundle (A'.coord 1) (B'.coord 0) :=
    Stacks.PullbackTensorIso.pullbackGlobalSections_tensorSectionsAt g _ _ _ _
  let z₁₂ := pullbackGlobalSections g (projectiveLineDiagonalPositiveTwist X)
    (projectiveLineCoordinateTensor X 0 1)
  let z₂₁ := pullbackGlobalSections g (projectiveLineDiagonalPositiveTwist X)
    (projectiveLineCoordinateTensor X 1 0)
  have hz : pullbackGlobalSections g (projectiveLineDiagonalPositiveTwist X)
        (projectiveLineDiagonalDeterminant X) = 0 ↔ Isomorphic A' B' := by
    calc
      _ ↔ z₁₂ = z₂₁ := by rw [projectiveLineDiagonalDeterminant, map_sub, sub_eq_zero]
      _ ↔ φ z₁₂ = φ z₂₁ := hinj.eq_iff.symm
      _ ↔ CrossMultiplies A'.coord B'.coord := by
        rw [show φ z₁₂ = _ from h₁₂, show φ z₂₁ = _ from h₂₁]
        exact (crossMultiplies_iff_determinant_eq A' B').symm
      _ ↔ Isomorphic A' B' := crossMultiplies_iff_isomorphic
  have hA : (⟦A'⟧ : Points T 1) = pointsOfHom ((g ≫ p₁) ≫ τ) := by
    rw [Category.assoc, pointsOfHom_comp g, pointsOfHom_comp p₁]
    rfl
  have hB : (⟦B'⟧ : Points T 1) = pointsOfHom ((g ≫ p₂) ≫ τ) := by
    rw [Category.assoc, pointsOfHom_comp g, pointsOfHom_comp p₂]
    rfl
  rw [hz]
  constructor
  · intro h
    have heq := pointsOfHom_injective (hA.symm.trans ((Quotient.sound h).trans hB))
    refine pullback.hom_ext ?_ heq
    change (g ≫ p₁) ≫ π = (g ≫ p₂) ≫ π
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun q : Q ⟶ X => g ≫ q) (pullback.condition (f := π) (g := π))).trans
        (Category.assoc _ _ _).symm)
  · intro h
    exact Quotient.exact (hA.trans ((congrArg pointsOfHom (congrArg (· ≫ τ) h)).trans hB.symm))

end AlgebraicGeometry.Scheme
