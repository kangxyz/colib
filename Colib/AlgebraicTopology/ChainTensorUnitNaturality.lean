/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicTopology.ChainTensorUnitTransport
/-! # Naturality of the actual chain right-unit insertion -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicTopology
variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasZeroObject C] [HasFiniteCoproducts C]

omit [HasFiniteCoproducts C] in
/-- The actual chain right unitor is natural, without adding a separate monoidal
structure or stronger preservation hypotheses on the chain category. -/
theorem chainRightUnitor_inv_naturality {K L : ChainComplex C ℕ} (f : K ⟶ L) :
    f ≫ (HomologicalComplex.rightUnitor L).inv =
      (HomologicalComplex.rightUnitor K).inv ≫
        HomologicalComplex.tensorHom f (𝟙 (HomologicalComplex.tensorUnit C (.down ℕ))) := by
  ext n : 1
  change f.f n ≫ (HomologicalComplex.rightUnitor' L).inv n =
    (HomologicalComplex.rightUnitor' K).inv n ≫
      (HomologicalComplex.tensorHom f (𝟙 (HomologicalComplex.tensorUnit C (.down ℕ)))).f n
  rw [HomologicalComplex.rightUnitor'_inv, HomologicalComplex.rightUnitor'_inv,
    Category.assoc, Category.assoc, HomologicalComplex.ι_mapBifunctorMap]
  simp only [ChainComplex.single₀ObjXSelf, Iso.refl_inv, HomologicalComplex.id_f,
    curriedTensor_map_app, curriedTensor_obj_map]
  erw [whiskerLeft_id, whiskerLeft_id]
  erw [Category.id_comp, Category.id_comp]
  exact rightUnitor_inv_naturality_assoc (f.f n) _

/-- A map before native unit-coordinate insertion moves into the first tensor factor. -/
theorem chainUnitCoordinate_naturality {K L M : ChainComplex C ℕ} (a : K ⟶ L)
    (b : HomologicalComplex.tensorUnit C (.down ℕ) ⟶ M) :
    a ≫ ((HomologicalComplex.rightUnitor L).inv ≫ HomologicalComplex.tensorHom (𝟙 L) b) =
      (HomologicalComplex.rightUnitor K).inv ≫ HomologicalComplex.tensorHom a b := by
  rw [← Category.assoc, chainRightUnitor_inv_naturality, Category.assoc, chainTensorHom_comp,
    Category.comp_id, Category.id_comp]

/-- A first-factor map and both genuine comparisons enter the two coordinate
factors after the unchanged native right-unit insertion. -/
theorem chainUnitCoordinate_fullTransport {K L L' M M' : ChainComplex C ℕ}
    (a : K ⟶ L) (b : HomologicalComplex.tensorUnit C (.down ℕ) ⟶ M)
    (e : L ⟶ L') (f : M ⟶ M') :
    (a ≫ ((HomologicalComplex.rightUnitor L).inv ≫ HomologicalComplex.tensorHom (𝟙 L) b)) ≫
      HomologicalComplex.tensorHom e f =
    (HomologicalComplex.rightUnitor K).inv ≫
      HomologicalComplex.tensorHom (a ≫ e) (b ≫ f) := by
  rw [chainUnitCoordinate_naturality, chainUnitCoordinate_transport]

end AlgebraicTopology
