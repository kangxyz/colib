/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.DiagonalBaseChangeComparison
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.DiagonalProjectedSequence
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.GeometricCoefficientFunctors
public import Colib.AlgebraicGeometry.ProjectiveLine.DiagonalQuotientNaturality

/-! # The middle coefficient is pullback after the first direct image

On the actual Godement representative, the underived base-change mate
followed by the pushed augmentation is a weak natural comparison. No
inverse quasi-isomorphism of complexes is chosen.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
open AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry.Scheme.Modules.FlasquePerfect

universe u

set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{u})

local notation "P" => projectiveSpaceOver 1 X
local notation "π" => (P ↘ X)
local notation "Q" => CategoryTheory.Limits.pullback π π
local notation "p₁" => CategoryTheory.Limits.pullback.fst π π
local notation "p₂" => CategoryTheory.Limits.pullback.snd π π
local notation "c" => ComplexShape.up ℤ
local notation "B" => BoundedBelowPerfect.projectiveLineDiagonalBoundedMiddle X
local notation "G" => projectiveLineG₀ X
local notation "F" => Functor.mapHomologicalComplex (pushforward p₁) c
local notation "T" => BoundedBelowPerfect.waldhausen P
local notation "W" => perfectComplexesWaldhausen
  (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace P))

local instance : IsProper π := isProper_projectiveSpaceOver 1 X

/-- Degreewise pullback is the middle term, by the canonical left unit law. -/
def projectiveLineDiagonalMiddleTermIso :
    (BoundedBelowPerfect.objects P).ι ⋙ (pullback p₂).mapHomologicalComplex c ≅
      B ⋙ (BoundedBelowPerfect.objects Q).ι :=
  let O := _root_.SheafOfModules.unit (Q).ringCatSheaf
  let A : (Q).Modules ⥤ (Q).Modules :=
    (Stacks.SheafOfModules.Tensor.sheafTensor (Q).sheaf).obj O
  let : A.PreservesZeroMorphisms :=
    Stacks.Sheaves.ChangeOfRings.preservesZeroMorphisms_sheafTensorObj (Q).sheaf O
  let Fpb := pullback p₂
  let e : Fpb ⋙ A ≅ Fpb :=
    Functor.isoWhiskerLeft Fpb (diagonalUnitTensorNatIso Q) ≪≫ Functor.rightUnitor Fpb
  Functor.isoWhiskerLeft (BoundedBelowPerfect.objects P).ι
    (Functor.mapHomologicalComplexCompIso e c).symm

/-- The natural chain map from the pullback of the actual untwisted coefficient
to the projected middle term evaluated at a flasque source. -/
def projectiveLineDiagonalMiddleComparison :
    G ⋙ perfectFlatPullback π ⟶
      inclusion P ⋙ projectiveLineDiagonalProjectedMiddle X :=
  let i := inclusion P ⋙ (BoundedBelowPerfect.objects P).ι
  let e := projectiveLineDiagonalMiddleTermIso X
  let η := Functor.whiskerRight
    (Functor.whiskerLeft (inclusion P ⋙ B) (unit Q))
    ((BoundedBelowPerfect.objects Q).ι ⋙ F)
  let θ := Functor.whiskerLeft i (projectiveLineDiagonalBaseChangeCochain X) ≫
    Functor.whiskerRight (Functor.whiskerLeft (inclusion P) e.hom) F ≫ η
  { app J := ObjectProperty.homMk (θ.app J)
    naturality {_ _} f := by
      apply ObjectProperty.hom_ext
      exact θ.naturality f }

/-- This is the base-change quasi-isomorphism for the literal cochain representatives. -/
theorem projectiveLineDiagonalMiddleComparison_weak (J : Obj P) :
    (W).weq ((projectiveLineDiagonalMiddleComparison X).app J) := by
  let K := (inclusion P).obj J
  let A := (B).obj K
  let J' := (total Q).obj A
  let e := (projectiveLineDiagonalMiddleTermIso X).hom.app K
  let a := ((unit Q).app A).hom
  have : QuasiIso a := unit_weak Q A
  have : QuasiIso (e ≫ a) := inferInstance
  have h := projectiveLineDiagonalBaseChangeCochain_comp_quasiIso X J.obj J'.obj
    J.property.1.1 J.property.1.2 J'.property.1.2 J.property.2 J'.property.2 (e ≫ a)
  change QuasiIso ((projectiveLineDiagonalBaseChangeCochain X).app J.obj ≫
    (F).map e ≫ (F).map a)
  simpa only [Functor.map_comp, Category.assoc] using h

end AlgebraicGeometry.Scheme.Modules.FlasquePerfect
