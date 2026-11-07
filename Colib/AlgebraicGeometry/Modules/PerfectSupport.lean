/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectOpenWeak

/-! # Support on the complement of an open immersion

Support means acyclic after actual degreewise restriction. The category consists
of actual complexes with native Stacks perfectness, not a derived replacement.
Adapted from Quillen PerfectSupport/OpenSupport at c561118b.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
open Waldhausen Fibration
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]

/-- Native perfect complexes acyclic on the specified open immersion. -/
def perfectSupported : ObjectProperty (CochainComplex X.Modules ℤ) := fun K =>
  RingedSpace.IsPerfectComplex (X := X.toRingedSpace) K ∧
    (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic

/-- Relative acyclicity is exactly acyclicity of the restricted complex in every degree. -/
theorem perfectOpenAcyclic_iff
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    Acyclic (perfectOpenWeakWaldhausen j) K ↔
      (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj K.obj).Acyclic := by
  let F := (restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)
  let V := RingedSpace.perfectComplexesWaldhausen X.toRingedSpace
  have hZ : IsZero (F.obj V.zero.obj) := F.map_isZero
    ((CofibrationClosedSubcategory.inclusion_exact (complexes X.Modules) _
      (RingedSpace.perfectComplexes_cofibrationClosed X.toRingedSpace)).zero V.isZero)
  change QuasiIso (F.map (V.isZero.to_ K).hom) ↔ _
  rw [quasiIso_iff]
  exact forall_congr' fun n => quasiIsoAt_iff_exactAt _ n
    (HomologicalComplex.acyclic_of_isZero _ hZ n)

/-- Support is closed under the actual ambient zero and ambient Mono pushouts. -/
theorem perfectSupported_cofibrationClosed :
    CofibrationClosedSubcategory.Closed (complexes X.Modules) (perfectSupported j) where
  zero_mem := by
    refine ⟨(RingedSpace.perfectComplexes_cofibrationClosed X.toRingedSpace).zero_mem, ?_⟩
    exact HomologicalComplex.acyclic_of_isZero _
      (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map_isZero
        (complexes X.Modules).isZero)
  pushout_mem {A B D Q} {i f g k} hi h hA hB hD := by
    let P : ObjectProperty (CochainComplex X.Modules ℤ) :=
      RingedSpace.IsPerfectComplex (X := X.toRingedSpace)
    have hQ : P Q := (RingedSpace.perfectComplexes_cofibrationClosed X.toRingedSpace).pushout_mem
      hi h hA.1 hB.1 hD.1
    let A' : P.FullSubcategory := ⟨A, hA.1⟩
    let B' : P.FullSubcategory := ⟨B, hB.1⟩
    let D' : P.FullSubcategory := ⟨D, hD.1⟩
    let Q' : P.FullSubcategory := ⟨Q, hQ⟩
    let i' : A' ⟶ B' := P.homMk i
    let f' : A' ⟶ D' := P.homMk f
    let g' : B' ⟶ Q' := P.homMk g
    let j' : D' ⟶ Q' := P.homMk k
    have hp : IsPushout i' f' g' j' := IsPushout.of_map_of_faithful P.ι h
    exact ⟨hQ, (perfectOpenAcyclic_iff j Q').1
      (acyclic_of_isPushout (perfectOpenWeakWaldhausen j) hi hp
        ((perfectOpenAcyclic_iff j A').2 hA.2)
        ((perfectOpenAcyclic_iff j B').2 hB.2)
        ((perfectOpenAcyclic_iff j D').2 hD.2))⟩

/-- The actual supported full category inherits ambient Mono and QuasiIso. -/
def perfectSupportedWaldhausen : Waldhausen.Structure (perfectSupported j).FullSubcategory :=
  CofibrationClosedSubcategory.waldhausenStructure (complexes X.Modules)
    (perfectSupported j) (perfectSupported_cofibrationClosed j)

/-- Forget support, preserving the actual complex and map. -/
def perfectSupportedInclusion := ObjectProperty.ιOfLE
  (show perfectSupported j ≤ RingedSpace.IsPerfectComplex (X := X.toRingedSpace)
    from fun _ h => h.1)

/-- The actual supported inclusion is exact for the native fine structures. -/
theorem perfectSupportedInclusion_isExact :
    IsExact (perfectSupportedWaldhausen j).cof (perfectSupportedWaldhausen j).weq
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).cof
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).weq
      (perfectSupportedInclusion j) where
  zero h := by
    apply IsZero.of_full_of_faithful_of_isZero
      (ObjectProperty.ι (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))
    exact (CofibrationClosedSubcategory.inclusion_exact (complexes X.Modules)
      (perfectSupported j) (perfectSupported_cofibrationClosed j)).zero h
  cofibration _ h := h
  weak _ h := h
  pushout hi h := by
    apply IsPushout.of_map_of_faithful
      (ObjectProperty.ι (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))
    exact CofibrationClosedSubcategory.inclusion_map_pushout (complexes X.Modules)
      (perfectSupported j) (perfectSupported_cofibrationClosed j) hi h
end AlgebraicGeometry.Scheme.Modules
