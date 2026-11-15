/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Algebra.Homology.MapChainLaxTensor
/-! # Composition of the original additive lax chain tensor comparisons -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
namespace CategoryTheory.Functor
variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Preadditive C] [Preadditive D] [Preadditive E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
  [MonoidalPreadditive C] [MonoidalPreadditive D] [MonoidalPreadditive E]
  [HasCoproducts.{0} C] [HasCoproducts.{0} D] [HasCoproducts.{0} E]
  (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [F.LaxMonoidal] [G.LaxMonoidal]

/-- The chain tensorator of the original composite factors through the two original
one-way tensorators, without imposing preservation of coproducts on either functor. -/
theorem mapChainLaxTensor_comp (K L : ChainComplex C ℕ) :
    (F ⋙ G).mapChainLaxTensor K L =
      G.mapChainLaxTensor ((F.mapHomologicalComplex (.down ℕ)).obj K)
        ((F.mapHomologicalComplex (.down ℕ)).obj L) ≫
      (G.mapHomologicalComplex (.down ℕ)).map (F.mapChainLaxTensor K L) := by
  ext n : 1
  apply mapBifunctor.hom_ext
  intro p q h
  change ιTensorObj _ _ p q n h ≫ ((F ⋙ G).mapChainLaxTensor K L).f n =
    ιTensorObj _ _ p q n h ≫
      ((G.mapChainLaxTensor ((F.mapHomologicalComplex (.down ℕ)).obj K)
        ((F.mapHomologicalComplex (.down ℕ)).obj L)).f n ≫
        G.map ((F.mapChainLaxTensor K L).f n))
  rw [ι_mapChainLaxTensor, ι_mapChainLaxTensor_assoc, ← G.map_comp,
    ι_mapChainLaxTensor, G.map_comp]
  simp only [LaxMonoidal.comp_μ, comp_obj, comp_map, Category.assoc]
  rfl

end CategoryTheory.Functor
