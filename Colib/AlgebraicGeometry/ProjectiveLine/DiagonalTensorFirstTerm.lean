/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.DiagonalTensorTerms
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensor
public import StacksFrontier.AlgebraicGeometry.PullbackTensorIso.Invertible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsShortExact

/-! # The left term in the diagonal resolution with coefficients

The first term has one negative twist on each factor. The twist on the second
factor combines with the coefficient before pullback. The comparison is natural
in the coefficient and so applies degreewise to complexes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Stacks.RelativeVeryAmple Stacks.AlgebraicGeometry.ProjTwistTensorPow

set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u})

local notation "P" => projectiveSpaceOver 1 X
local notation "π" => (P ↘ X)
local notation "Q" => pullback π π
local notation "p₁" => pullback.fst π π
local notation "p₂" => pullback.snd π π
local notation "L" => twistOver 1 X (-1)
local notation "L₁" => Functor.obj (Modules.pullback p₁) L
local notation "L₂" => Functor.obj (Modules.pullback p₂) L
local notation "S" => projectiveLineDiagonalSequence X

local instance {Z : Scheme.{u}} : MonoidalCategory Z.Modules :=
  SheafOfModules.monoidalCategorySheafTensor Z.sheaf

/-- Tensor on the left by a fixed sheaf of modules. -/
abbrev projectiveLineTensorLeft {Z : Scheme.{u}} (A : Z.Modules) : Z.Modules ⥤ Z.Modules :=
  (Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf).obj A

instance {Z : Scheme.{u}} (A : Z.Modules) :
    (projectiveLineTensorLeft A).PreservesZeroMorphisms :=
  Stacks.Sheaves.ChangeOfRings.preservesZeroMorphisms_sheafTensorObj Z.sheaf A

/-- The actual first term of the diagonal sequence as a functor of the coefficient. -/
abbrev projectiveLineDiagonalFirstTermFunctor : (P).Modules ⥤ (Q).Modules :=
  Modules.pullback p₂ ⋙ projectiveLineTensorLeft (S).X₁

instance : (projectiveLineDiagonalFirstTermFunctor X).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_comp (Modules.pullback p₂) (projectiveLineTensorLeft (S).X₁)

/-- The pullback–tensor comparison with a fixed left factor. -/
def diagonalPullbackTensorLeftIso {Z Y : Scheme.{u}} (f : Z ⟶ Y) (A : Y.Modules) :
    projectiveLineTensorLeft A ⋙ Modules.pullback f ≅
      Modules.pullback f ⋙ projectiveLineTensorLeft ((Modules.pullback f).obj A) :=
  let e := Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom
  NatIso.ofComponents (fun B => e.app (A, B)) (fun {B B'} g => by
    have h := e.hom.naturality (X := (A, B)) (Y := (A, B')) (𝟙 A, g)
    change
      (Modules.pullback f).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).map (𝟙 A)).app B ≫
            (projectiveLineTensorLeft A).map g) ≫ (e.app (A, B')).hom =
        (e.app (A, B)).hom ≫
          (((Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf).map
            ((Modules.pullback f).map (𝟙 A))).app ((Modules.pullback f).obj B) ≫
            (projectiveLineTensorLeft ((Modules.pullback f).obj A)).map
              ((Modules.pullback f).map g)) at h
    have hiY : (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).map (𝟙 A) =
        𝟙 (projectiveLineTensorLeft A) := CategoryTheory.Functor.map_id _ _
    have hiZ : (Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf).map
          ((Modules.pullback f).map (𝟙 A)) =
        𝟙 (projectiveLineTensorLeft ((Modules.pullback f).obj A)) := by
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rw [hiY, hiZ] at h
    simp only [NatTrans.id_app] at h
    erw [Category.id_comp] at h
    exact h)

/-- The first term with coefficients is
`p₁^*𝒪(-1) ⊗ p₂^*(𝒪(-1) ⊗ E)`, naturally in `E`. -/
def projectiveLineDiagonalFirstTermReshuffle :
    projectiveLineDiagonalFirstTermFunctor X ≅
      (projectiveLineTensorLeft L ⋙ Modules.pullback p₂) ⋙ projectiveLineTensorLeft L₁ :=
  Functor.isoWhiskerLeft (Modules.pullback p₂)
    (((Stacks.SheafOfModules.Tensor.sheafTensor (Q).sheaf).mapIso
      (projectiveLineDiagonalSequenceFirstIso X)).symm ≪≫
      tensorLeftTensor L₁ L₂) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (diagonalPullbackTensorLeftIso p₂ L).symm _

/-- The same comparison on cochain complexes, natural in the complex. -/
def projectiveLineDiagonalFirstTermReshuffleCochain :
    (projectiveLineDiagonalFirstTermFunctor X).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      ((projectiveLineTensorLeft L ⋙ Modules.pullback p₂) ⋙
        projectiveLineTensorLeft L₁).mapHomologicalComplex (ComplexShape.up ℤ) :=
  NatIso.mapHomologicalComplex (projectiveLineDiagonalFirstTermReshuffle X) _

end AlgebraicGeometry.Scheme
