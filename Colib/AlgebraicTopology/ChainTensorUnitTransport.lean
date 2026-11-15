/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import StacksFrontier.AlgebraicTopology.AlexanderWhitneyConstant
/-! # Native chain tensor functoriality and unit-coordinate transport -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicTopology
variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasZeroObject C] [HasFiniteCoproducts C]

omit [HasZeroObject C] in
/-- Both genuine chain tensor factors preserve composition simultaneously. -/
theorem chainTensorHom_comp {K K' K'' L L' L'' : ChainComplex C ℕ}
    (f : K ⟶ K') (f' : K' ⟶ K'') (g : L ⟶ L') (g' : L' ⟶ L'') :
    HomologicalComplex.tensorHom f g ≫ HomologicalComplex.tensorHom f' g' =
      HomologicalComplex.tensorHom (f ≫ f') (g ≫ g') := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine HomologicalComplex.mapBifunctor.hom_ext fun i j h => ?_
  simp [HomologicalComplex.ι_mapBifunctorMap_assoc, HomologicalComplex.ι_mapBifunctorMap,
    whisker_exchange_assoc]

/-- Both comparison maps enter the actual coordinate tensor factors, retaining
rather than redefining the native right unit and tensor map. -/
theorem chainUnitCoordinate_transport {K L L' M M' : ChainComplex C ℕ}
    (a : K ⟶ L) (b : HomologicalComplex.tensorUnit C (.down ℕ) ⟶ M)
    (e : L ⟶ L') (f : M ⟶ M') :
    ((HomologicalComplex.rightUnitor K).inv ≫ HomologicalComplex.tensorHom a b) ≫
      HomologicalComplex.tensorHom e f =
    (HomologicalComplex.rightUnitor K).inv ≫
      HomologicalComplex.tensorHom (a ≫ e) (b ≫ f) := by
  rw [Category.assoc, chainTensorHom_comp]

end AlgebraicTopology
