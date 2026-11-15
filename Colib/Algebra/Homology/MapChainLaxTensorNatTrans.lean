/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Algebra.Homology.MapChainLaxTensor
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
/-! # The native lax chain tensor comparison respects monoidal natural transformations -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
namespace CategoryTheory.Functor
variable {C D : Type*} [Category C] [Category D]
  [Preadditive C] [Preadditive D] [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  [HasCoproducts.{0} C] [HasCoproducts.{0} D]
  {F G : C ⥤ D} [F.Additive] [G.Additive] [F.LaxMonoidal] [G.LaxMonoidal]
  (τ : F ⟶ G) [NatTrans.IsMonoidal τ]

/-- The coefficient-level monoidal square lifts to the original total chain tensors.
Neither the transformation nor the tensor comparisons are assumed invertible. -/
theorem mapChainLaxTensor_natTrans (K L : ChainComplex C ℕ) :
    F.mapChainLaxTensor K L ≫
      (NatTrans.mapHomologicalComplex τ (.down ℕ)).app (tensorObj K L) =
    tensorHom ((NatTrans.mapHomologicalComplex τ (.down ℕ)).app K)
      ((NatTrans.mapHomologicalComplex τ (.down ℕ)).app L) ≫ G.mapChainLaxTensor K L := by
  ext n : 1
  simp only [HomologicalComplex.comp_f]
  apply mapBifunctor.hom_ext
  intro p q h
  simp only [ι_mapChainLaxTensor_assoc, ι_mapChainLaxTensor, ι_mapBifunctorMap_assoc,
    curriedTensor_map_app, curriedTensor_obj_map]
  change LaxMonoidal.μ F (K.X p) (L.X q) ≫
      F.map (ιTensorObj K L p q n h) ≫ τ.app _ =
    (τ.app (K.X p) ▷ F.obj (L.X q)) ≫ (G.obj (K.X p) ◁ τ.app (L.X q)) ≫
      LaxMonoidal.μ G (K.X p) (L.X q) ≫ G.map (ιTensorObj K L p q n h)
  rw [τ.naturality, ← Category.assoc, NatTrans.IsMonoidal.tensor]
  simp only [tensorHom_def, Category.assoc]

end CategoryTheory.Functor
