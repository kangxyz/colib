/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.EulerTerms
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoverTensorExactness
public import StacksFrontier.AlgebraicGeometry.FiberRank.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.ComplexesOfModules

/-! # The Euler sequence with arbitrary coefficients

The quotient of the coordinate Koszul sequence is the structure sheaf, hence flat.
Tensoring it with any module preserves the actual short exact sequence, including
the original arrows. No flatness of the input module is required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u})

local notation "P" => projectiveSpaceOver 1 X

local instance : MonoidalCategory (P).Modules :=
  SheafOfModules.monoidalCategorySheafTensor (P).sheaf

local instance : MonoidalPreadditive (P).Modules := by
  let := Abelian.hasFiniteBiproducts (C := (P).Modules)
  exact SheafOfModules.monoidalPreadditiveSheafTensor (P).sheaf

/-- Tensoring the actual projective-line Euler sequence with an arbitrary module is exact. -/
theorem projectiveLineEulerSequence_tensor_shortExact (M : (P).Modules) :
    ((projectiveLineEulerSequence X).map
      (MonoidalCategory.tensorRight M)).ShortExact := by
  let : _root_.SheafOfModules.IsLocallyFree.{u, u, u}
      (R := (P).ringCatSheaf) (projectiveLineEulerSequence X).X₃ := by
    obtain ⟨q, hq, _⟩ :=
      (projectiveLineEulerLast_finiteLocallyFree X).exists_isFiniteLocallyFreeData
    exact ⟨q, hq⟩
  obtain ⟨_, h⟩ := Stacks.SheafOfModules.FlatCover.sheafTensorRight_shortExact_of_isFlat_X₃
    (P).sheaf (projectiveLineEulerSequence X) M (projectiveLineEulerSequence_shortExact X)
    (AlgebraicGeometry.Scheme.Modules.isFlat_of_isLocallyFree (X := projectiveSpaceOver 1 X)
      (projectiveLineEulerSequence X).X₃)
  exact h

end AlgebraicGeometry.Scheme
