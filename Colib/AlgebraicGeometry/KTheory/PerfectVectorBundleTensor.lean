/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectWaldhausen
public import Colib.CategoryTheory.Waldhausen.ExactFunctorIso
public import Colib.Util.References
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatnessAndRightExactness
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TensorProduct
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.ComplexesOfModules
public import StacksFrontier.Homology.TensorComplex.SingleTensor
public import StacksFrontier.AlgebraicGeometry.FiberRank.Basic

/-! # Tensoring perfect complexes with a vector bundle

The degreewise tensor functors are exact for the native Waldhausen structure of perfect
complexes. For perfectness, place the bundle in degree zero and use the actual total tensor
complex; flatness makes the degree-zero bundle K-flat.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}} (L : X.Modules)

local instance tensorMonoidal : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategorySheafTensor X.sheaf

local instance tensorAdditive : MonoidalPreadditive X.Modules := by
  let := Abelian.hasFiniteBiproducts (C := X.Modules)
  exact SheafOfModules.monoidalPreadditiveSheafTensor X.sheaf

local instance tensorSymmetric : SymmetricCategory X.Modules :=
  SheafOfModules.symmetricCategorySheafTensor X.sheaf

local instance complexMonoidal : MonoidalCategory (CochainComplex X.Modules ℤ) :=
  Stacks.Cohomology.MonoidalComplexesOfModules.cochainComplexMonoidalCategory X.sheaf

local instance complexSymmetric : SymmetricCategory (CochainComplex X.Modules ℤ) :=
  Stacks.Cohomology.MonoidalComplexesOfModules.cochainComplexSymmetricCategory X.sheaf

local notation "Perf" =>
  ObjectProperty.FullSubcategory
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))

variable [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L]

set_option backward.isDefEq.respectTransparency false in
/-- Degreewise left tensor by a vector bundle preserves perfect complexes. -/
theorem Complex.isPerfectComplex_tensorLeft (K : CochainComplex X.Modules ℤ)
    (hK : RingedSpace.IsPerfectComplex (X := X.toRingedSpace) K) :
    RingedSpace.IsPerfectComplex (X := X.toRingedSpace)
      (((tensorLeft L).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  let A := (CochainComplex.singleFunctor X.Modules 0).obj L
  have hA := isPerfectComplex_single_of_isFiniteLocallyFree X L inferInstance
  have hAf := kFlat_single_of_isFiniteLocallyFree X L inferInstance
  have hKA := RingedSpace.isPerfectComplex_tensorComplex hK hA hAf
  let e := (β_ K A) ≪≫ TotalTensorComplex.SingleTensor.singleTensorIso L K
  exact hKA.of_quasiIso e.hom inferInstance

/-- Tensor each term on the left by the given vector bundle. -/
def perfectTensorLeft : Perf ⥤ Perf :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ (tensorLeft L).mapHomologicalComplex (ComplexShape.up ℤ))
    (fun K => Complex.isPerfectComplex_tensorLeft L K.obj K.property)

set_option backward.isDefEq.respectTransparency false in
/-- Degreewise right tensor by a vector bundle preserves perfect complexes. -/
theorem Complex.isPerfectComplex_tensorRight (K : CochainComplex X.Modules ℤ)
    (hK : RingedSpace.IsPerfectComplex (X := X.toRingedSpace) K) :
    RingedSpace.IsPerfectComplex (X := X.toRingedSpace)
      (((tensorRight L).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  (Complex.isPerfectComplex_tensorLeft L K hK).of_quasiIso
    ((NatIso.mapHomologicalComplex (BraidedCategory.tensorLeftIsoTensorRight L)
      (ComplexShape.up ℤ)).app K).hom
    inferInstance

/-- Tensor each term on the right by the given vector bundle. -/
def perfectTensorRight : Perf ⥤ Perf :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ (tensorRight L).mapHomologicalComplex (ComplexShape.up ℤ))
    (fun K => Complex.isPerfectComplex_tensorRight L K.obj K.property)

/-- The two tensor orders are identified by the degreewise braiding. -/
def perfectTensorLeftRightIso : perfectTensorLeft L ≅ perfectTensorRight L :=
  NatIso.ofComponents
    (fun K => ObjectProperty.isoMk
      (P := RingedSpace.IsPerfectComplex (X := X.toRingedSpace))
      ((NatIso.mapHomologicalComplex (BraidedCategory.tensorLeftIsoTensorRight L)
        (ComplexShape.up ℤ)).app K.obj))
    (fun {_ _} f => by
      apply (ObjectProperty.ι _).map_injective
      exact (NatIso.mapHomologicalComplex (BraidedCategory.tensorLeftIsoTensorRight L)
        (ComplexShape.up ℤ)).hom.naturality f.hom)

local notation "W" => RingedSpace.perfectComplexesWaldhausen X.toRingedSpace

set_option backward.isDefEq.respectTransparency false in
/-- Degreewise tensor on the right by a vector bundle is Waldhausen exact. -/
theorem perfectTensorRight_waldhausenExact :
    Waldhausen.IsExact (W).cof (W).weq (W).cof (W).weq (perfectTensorRight L) := by
  let P : ObjectProperty (CochainComplex X.Modules ℤ) :=
    RingedSpace.IsPerfectComplex (X := X.toRingedSpace)
  let T := tensorRight L
  let F := T.mapHomologicalComplex (ComplexShape.up ℤ)
  have hT : exactFunctor _ _ T := by
    change exactFunctor _ _ ((curriedTensor X.Modules).flip.obj L)
    exact Stacks.SheafOfModules.exactFunctor_sheafTensorFlip_of_isFlat X.sheaf L
      (isFlat_of_isFiniteLocallyFree L)
  obtain ⟨hlim, hcolim⟩ := (exactFunctor_iff _).mp hT
  refine { zero := ?_, cofibration := ?_, weak := ?_, pushout := ?_ }
  · intro Z hZ
    apply IsZero.of_full_of_faithful_of_isZero P.ι
    exact F.map_isZero
      ((Waldhausen.CofibrationClosedSubcategory.inclusion_exact
        (Waldhausen.complexes X.Modules) P
        (RingedSpace.perfectComplexes_cofibrationClosed X.toRingedSpace)).zero hZ)
  · intro K K' f hf
    change Mono (F.map f.hom)
    have : Mono (C := CochainComplex X.Modules ℤ) f.hom := hf
    infer_instance
  · intro K K' f hf
    change QuasiIso (F.map f.hom)
    have : QuasiIso (C := X.Modules) f.hom := hf
    infer_instance
  · intro A B D E i f g j hi h
    apply IsPushout.of_map_of_faithful P.ι
    exact (Waldhausen.CofibrationClosedSubcategory.inclusion_map_pushout
      (Waldhausen.complexes X.Modules) P
      (RingedSpace.perfectComplexes_cofibrationClosed X.toRingedSpace) hi h).map F

/-- Degreewise tensor on the left by a vector bundle is Waldhausen exact. -/
theorem perfectTensorLeft_waldhausenExact :
    Waldhausen.IsExact (W).cof (W).weq (W).cof (W).weq (perfectTensorLeft L) :=
  (perfectTensorRight_waldhausenExact L).of_iso (perfectTensorLeftRightIso L).symm

end AlgebraicGeometry.Scheme.Modules

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/LineTensor.lean:61-74"
  "generalization" "Degreewise tensor exactness for finite locally free coefficients"]
  AlgebraicGeometry.Scheme.Modules.perfectTensorLeft_waldhausenExact
