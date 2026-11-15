/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Algebra.Homology.MapChainLaxTensor
public import StacksFrontier.Homology.MapHomologicalComplexMonoidal
/-! # Identifying the one-way chain comparison with the existing strong tensorator -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
namespace CategoryTheory.Functor
variable {C D : Type*} [Category C] [Category D]
  [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
  [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  [HasCoproducts.{0} C] [HasCoproducts.{0} D]
  (F : C ⥤ D) [F.Additive] [F.Monoidal] [PreservesColimitsOfSize.{0, 0} F]

/-- Where the original strong chain tensorator exists, the one-way comparison is
its original hom, not a second choice of tensor map. -/
theorem mapChainLaxTensor_eq_tensorator (K L : ChainComplex C ℕ) :
    F.mapChainLaxTensor K L = (F.mapHomologicalComplexTensorator K L).hom := by
  ext n : 1
  apply mapBifunctor.hom_ext
  intro p q h
  rw [ι_mapChainLaxTensor, ι_mapHomologicalComplexTensorator_hom]

end CategoryTheory.Functor
