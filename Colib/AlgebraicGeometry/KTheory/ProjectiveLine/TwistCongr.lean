/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.SupportedTwist

/-! # Native tensor functor under an isomorphism of bundles -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}} (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L]

local notation "TX" => Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf

/-- An isomorphism of vector bundles induces an isomorphism of their actual tensor functors. -/
def perfectTensorLeft_congr {L' : X.Modules}
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L']
    (e : L ≅ L') : perfectTensorLeft L ≅ perfectTensorLeft L' :=
  Functor.fullyFaithfulCancelRight
    (ObjectProperty.ι (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))
    (Functor.isoWhiskerLeft
      (ObjectProperty.ι (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))
      (NatIso.mapHomologicalComplex
        (F := Scheme.projectiveLineTensorLeft L)
        (G := Scheme.projectiveLineTensorLeft L') ((TX).mapIso e) (.up ℤ)))

variable {Y : Scheme.{u}} (f : Y ⟶ X) [Flat f] (M : Y.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M]

/-- Native pullback commutes with the actual degreewise left-tensor functor. -/
def perfectTensorLeft_pullbackIso (e : (pullback f).obj L ≅ M) :
    perfectTensorLeft L ⋙ perfectFlatPullback f ≅
      perfectFlatPullback f ⋙ perfectTensorLeft M := by
  let T : X.Modules ⥤ X.Modules := Scheme.projectiveLineTensorLeft L
  let R : X.Modules ⥤ Y.Modules := pullback f
  let T' : Y.Modules ⥤ Y.Modules := Scheme.projectiveLineTensorLeft M
  let : T.PreservesZeroMorphisms := inferInstanceAs
    (Scheme.projectiveLineTensorLeft L).PreservesZeroMorphisms
  let : R.PreservesZeroMorphisms := inferInstanceAs (pullback f).PreservesZeroMorphisms
  let : T'.PreservesZeroMorphisms := inferInstanceAs
    (Scheme.projectiveLineTensorLeft M).PreservesZeroMorphisms
  let d : T ⋙ R ≅ R ⋙ T' := Scheme.diagonalPullbackTensorLeftIso f L ≪≫
    Functor.isoWhiskerLeft R ((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).mapIso e)
  let dc := (Functor.mapHomologicalComplexCompIso (F := T) (G := R) (H := R ⋙ T') d (.up ℤ)) ≪≫
    (Functor.mapHomologicalComplexCompIso (F := R) (G := T') (H := R ⋙ T')
      (Iso.refl (R ⋙ T')) (.up ℤ)).symm
  exact Functor.fullyFaithfulCancelRight
    (ObjectProperty.ι (RingedSpace.IsPerfectComplex (X := Y.toRingedSpace)))
    (Functor.isoWhiskerLeft
      (ObjectProperty.ι (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) dc)

end AlgebraicGeometry.Scheme.Modules
