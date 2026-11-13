/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.DiagonalTensorExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # The diagonal ideal sequence with cochain coefficients -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u})

local notation "P" => projectiveSpaceOver 1 X
local notation "π" => (P ↘ X)
local notation "Q" => pullback π π
local notation "p₂" => pullback.snd π π
local notation "S" => projectiveLineDiagonalSequence X

local instance (A : (Q).Modules) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor (Q).sheaf).obj A).PreservesZeroMorphisms :=
  Stacks.Sheaves.ChangeOfRings.preservesZeroMorphisms_sheafTensorObj (Q).sheaf A

/-- The term functor of the diagonal resolution at a fixed module on the square. -/
abbrev projectiveLineDiagonalCochainTerm (A : (Q).Modules) :
    CochainComplex (P).Modules ℤ ⥤ CochainComplex (Q).Modules ℤ :=
  ((Modules.pullback p₂).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
    (((Stacks.SheafOfModules.Tensor.sheafTensor (Q).sheaf).obj A).mapHomologicalComplex
      (ComplexShape.up ℤ))

/-- A morphism of terms of the diagonal ideal sequence acts naturally on the coefficient. -/
def projectiveLineDiagonalCochainTermMap {A B : (Q).Modules} (h : A ⟶ B) :
    projectiveLineDiagonalCochainTerm X A ⟶ projectiveLineDiagonalCochainTerm X B :=
  Functor.whiskerLeft ((Modules.pullback p₂).mapHomologicalComplex (ComplexShape.up ℤ))
    ((((Stacks.SheafOfModules.Tensor.sheafTensor (Q).sheaf).map h)).mapHomologicalComplex
      (ComplexShape.up ℤ))

/-- The actual tensorized inclusion followed by the actual tensorized quotient is zero. -/
theorem projectiveLineDiagonalCochainTermMap_comp_zero :
    projectiveLineDiagonalCochainTermMap X (S).f ≫
      projectiveLineDiagonalCochainTermMap X (S).g = 0 := by
  apply NatTrans.ext
  funext K
  apply HomologicalComplex.hom_ext
  intro j
  let T := projectiveLineDiagonalCoefficientFunctor X (K.X j)
  change (T).map (S).f ≫ (T).map (S).g = 0
  rw [← Functor.map_comp, (S).zero, Functor.map_zero]

/-- The diagonal sequence after tensoring by each term of a cochain complex from the
second factor. Its maps are the actual ideal inclusion and quotient, tensored degreewise. -/
def projectiveLineDiagonalCochainSequence (K : CochainComplex (P).Modules ℤ) :
    ShortComplex (CochainComplex (Q).Modules ℤ) :=
  ShortComplex.mk ((projectiveLineDiagonalCochainTermMap X (S).f).app K)
    ((projectiveLineDiagonalCochainTermMap X (S).g).app K)
    (by simpa only [NatTrans.comp_app, NatTrans.app_zero] using
      NatTrans.congr_app (projectiveLineDiagonalCochainTermMap_comp_zero X) K)

/-- The actual cochain sequence is short exact in every degree. -/
theorem projectiveLineDiagonalCochainSequence_shortExact (K : CochainComplex (P).Modules ℤ) :
    (projectiveLineDiagonalCochainSequence X K).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro j
  exact projectiveLineDiagonalSequence_tensor_shortExact X (K.X j)

end AlgebraicGeometry.Scheme
