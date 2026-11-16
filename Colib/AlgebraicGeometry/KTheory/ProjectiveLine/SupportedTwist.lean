/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.TwistOpenRestriction
public import Colib.AlgebraicGeometry.Modules.PerfectSupportedFlatPullback

/-! # The actual twist preserves support -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
  (L : X.Modules) (M : Y.Modules)

local notation "TX" => Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf
local notation "TY" => Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf

local instance (A : X.Modules) : ((TX).obj A).PreservesZeroMorphisms :=
  Stacks.Sheaves.ChangeOfRings.preservesZeroMorphisms_sheafTensorObj X.sheaf A

local instance (A : Y.Modules) : ((TY).obj A).PreservesZeroMorphisms :=
  Stacks.Sheaves.ChangeOfRings.preservesZeroMorphisms_sheafTensorObj Y.sheaf A

/-- The genuine restriction of left tensor by the given bundle is left tensor by
the specified pullback bundle. -/
def tensorLeftOpenRestrictionCochainIso (e : (pullback j).obj L ≅ M) :
    ((TX).obj L).mapHomologicalComplex (.up ℤ) ⋙
      (restrictFunctor j).mapHomologicalComplex (.up ℤ) ≅
    (restrictFunctor j).mapHomologicalComplex (.up ℤ) ⋙
      ((TY).obj M).mapHomologicalComplex (.up ℤ) := by
  let T : X.Modules ⥤ X.Modules := (TX).obj L
  let R : X.Modules ⥤ Y.Modules := restrictFunctor j
  let T' : Y.Modules ⥤ Y.Modules := (TY).obj M
  let : T.PreservesZeroMorphisms :=
    Stacks.Sheaves.ChangeOfRings.preservesZeroMorphisms_sheafTensorObj X.sheaf L
  let : R.PreservesZeroMorphisms := inferInstanceAs ((restrictFunctor j).PreservesZeroMorphisms)
  let : T'.PreservesZeroMorphisms :=
    Stacks.Sheaves.ChangeOfRings.preservesZeroMorphisms_sheafTensorObj Y.sheaf M
  let d : T ⋙ R ≅ R ⋙ T' := tensorLeftOpenRestrictionModuleIso j L ≪≫
    Functor.isoWhiskerLeft R ((TY).mapIso e)
  exact (Functor.mapHomologicalComplexCompIso (F := T) (G := R) (H := R ⋙ T') d (.up ℤ)) ≪≫
    (Functor.mapHomologicalComplexCompIso (F := R) (G := T') (H := R ⋙ T')
      (Iso.refl (R ⋙ T')) (.up ℤ)).symm

variable [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M]

/-- Tensoring by the given bundle preserves the actual support predicate. -/
theorem perfectSupported_tensorLeft (e : (pullback j).obj L ≅ M)
    {K : CochainComplex X.Modules ℤ} (hK : perfectSupported j K) :
    perfectSupported j ((((TX).obj L).mapHomologicalComplex (.up ℤ)).obj K) := by
  let : MonoidalCategory Y.Modules := SheafOfModules.monoidalCategorySheafTensor Y.sheaf
  let : MonoidalPreadditive Y.Modules := by
    let := Abelian.hasFiniteBiproducts (C := Y.Modules)
    exact SheafOfModules.monoidalPreadditiveSheafTensor Y.sheaf
  let : ((TY).obj M).Additive := inferInstanceAs ((tensorLeft M).Additive)
  have hM := Stacks.SheafOfModules.exact_sheafTensorObj_of_isFlat
    Y.sheaf (isFlat_of_isFiniteLocallyFree M)
  obtain ⟨hlim, hcolim⟩ := (exactFunctor_iff _).1 hM
  refine ⟨Complex.isPerfectComplex_tensorLeft L K hK.1, ?_⟩
  have hA := acyclic_mapCochainComplex_of_preservesHomology ((TY).obj M) hK.2
  exact fun n => (hA n).of_iso ((tensorLeftOpenRestrictionCochainIso j L M e).app K).symm

/-- The actual left-tensor functor on the full subcategory of supported complexes. -/
def perfectSupportedTensorLeft (e : (pullback j).obj L ≅ M) :
    (perfectSupported j).FullSubcategory ⥤ (perfectSupported j).FullSubcategory :=
  (perfectSupported j).lift
    ((perfectSupported j).ι ⋙ ((TX).obj L).mapHomologicalComplex (.up ℤ))
    (fun K => perfectSupported_tensorLeft j L M e K.property)

/-- The supported left-tensor functor is Waldhausen exact. -/
theorem perfectSupportedTensorLeft_exact (e : (pullback j).obj L ≅ M) :
    Waldhausen.IsExact (perfectSupportedWaldhausen j).cof (perfectSupportedWaldhausen j).weq
      (perfectSupportedWaldhausen j).cof (perfectSupportedWaldhausen j).weq
      (perfectSupportedTensorLeft j L M e) := by
  let P := perfectSupported j
  let T : X.Modules ⥤ X.Modules := (TX).obj L
  let F := T.mapHomologicalComplex (ComplexShape.up ℤ)
  let : PreservesFiniteLimits T := (Stacks.SheafOfModules.exact_sheafTensorObj_of_isFlat
    X.sheaf (isFlat_of_isFiniteLocallyFree L)).1
  let : PreservesFiniteColimits T := (Stacks.SheafOfModules.exact_sheafTensorObj_of_isFlat
    X.sheaf (isFlat_of_isFiniteLocallyFree L)).2
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategorySheafTensor X.sheaf
  let : MonoidalPreadditive X.Modules := by
    let := Abelian.hasFiniteBiproducts (C := X.Modules)
    exact SheafOfModules.monoidalPreadditiveSheafTensor X.sheaf
  let : T.Additive := inferInstanceAs ((tensorLeft L).Additive)
  refine { zero := ?_, cofibration := ?_, weak := ?_, pushout := ?_ }
  · intro Z hZ
    apply IsZero.of_full_of_faithful_of_isZero P.ι
    exact F.map_isZero ((Waldhausen.CofibrationClosedSubcategory.inclusion_exact
      (Waldhausen.complexes X.Modules) P (perfectSupported_cofibrationClosed j)).zero hZ)
  · intro K K' f hf
    change Mono (F.map f.hom)
    have : Mono (C := CochainComplex X.Modules ℤ) f.hom := hf
    infer_instance
  · intro K K' f hf
    change QuasiIso (F.map f.hom)
    have : QuasiIso (C := X.Modules) f.hom := hf
    infer_instance
  · intro A B D E i f g l hi sq
    apply IsPushout.of_map_of_faithful P.ι
    exact (Waldhausen.CofibrationClosedSubcategory.inclusion_map_pushout
      (Waldhausen.complexes X.Modules) P
      (perfectSupported_cofibrationClosed j) hi sq).map F

end AlgebraicGeometry.Scheme.Modules
