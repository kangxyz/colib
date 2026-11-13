/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.Embedding.MapExtend
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived

/-! # Extension of the actual injective-resolution augmentation -/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Aglib/Algebra/Homology/DerivedCategory/ExtRightDerived.lean`,
blob `f97a4a1bd2958e794b08ef206cc1723b0337f77b`.
The canonical native objects and displayed maps are retained. Source candidate only.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open HomologicalComplex
universe w v u
namespace CategoryTheory
variable {C : Type u} [Category.{v} C]

/-- The additive version of conjugation by actual isomorphisms. -/
def Iso.homCongrAddEquiv [Preadditive C] {X Y X' Y' : C} (e : X ≅ X') (f : Y ≅ Y') :
    (X ⟶ Y) ≃+ (X' ⟶ Y') where
  toEquiv := Iso.homCongr e f
  map_add' a b := by simp [Iso.homCongr]

namespace InjectiveResolution
variable [Abelian C] {Y : C} (I : InjectiveResolution Y)

/-- The actual augmentation of the resolution extended by zero to integer degrees. -/
def extendedι : (CochainComplex.singleFunctor C 0).obj Y ⟶
    I.cocomplex.extend ComplexShape.embeddingUpNat :=
  (extendSingleIso ComplexShape.embeddingUpNat Y 0 0 rfl).inv ≫
    extendMap I.ι ComplexShape.embeddingUpNat

instance extendedι_quasiIso : QuasiIso I.extendedι := by
  dsimp only [extendedι]
  infer_instance

end InjectiveResolution

end CategoryTheory
