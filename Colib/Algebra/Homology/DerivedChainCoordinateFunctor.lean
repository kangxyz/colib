/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Algebra.Homology.DerivedChainCoordinate
/-! # Native coordinate comparison after an actual chain functor -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
open CochainComplex.KFlatBifunctor
namespace HomologicalComplex.TensorNegExtend
variable {C A : Type*} [Category C] [Category A]
  [Preadditive C] [HasZeroObject C] [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCoproducts.{0} C] [Abelian A] [MonoidalCategory A]
  [MonoidalPreadditive A] [HasCoproducts.{0} A] [HasDerivedCategory A]
  [(kFlatQLeft (curriedTensor A)).IsLocalization (kFlatQuasiIsoLeft (curriedTensor A))]
  [(kFlatQ (curriedTensor A)).IsLocalization (kFlatQuasiIso (curriedTensor A))]
  (hres : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
    KFlat (curriedTensor A) P ∧ QuasiIso f)

/-- A proved native unit/tensor law for the actual chain functor transports the
original coordinate insertion into the original derived tensor comparison. Neither the
unit map nor the tensorator in this statement is assumed invertible. -/
theorem derivedChainCoordinate_compare_functor
    (S : ChainComplex C ℕ ⥤ ChainComplex A ℕ)
    {X K L Z : ChainComplex C ℕ} (a : X ⟶ K)
    (b : HomologicalComplex.tensorUnit C (.down ℕ) ⟶ L)
    (u : HomologicalComplex.tensorUnit A (.down ℕ) ⟶
      S.obj (HomologicalComplex.tensorUnit C (.down ℕ)))
    (τ : HomologicalComplex.tensorObj (S.obj K) (S.obj L) ⟶
      S.obj (HomologicalComplex.tensorObj K L))
    (hunit : S.map ((HomologicalComplex.rightUnitor X).inv ≫
      HomologicalComplex.tensorHom a b) =
      (HomologicalComplex.rightUnitor (S.obj X)).inv ≫
        HomologicalComplex.tensorHom (S.map a) (u ≫ S.map b) ≫ τ)
    (c : HomologicalComplex.tensorObj K L ⟶ Z) :
    derivedChainCoordinate hres (S.map a) (u ≫ S.map b) ≫
      toTensor (curriedTensor A) hres (negExtend (S.obj K)) (negExtend (S.obj L)) ≫
      DerivedCategory.Q.map ((tensorNegExtendFullIso (S.obj K) (S.obj L)).hom ≫
        extendMap (τ ≫ S.map c) ComplexShape.embeddingDownNat) =
    DerivedCategory.Q.map (extendMap
      (S.map (((HomologicalComplex.rightUnitor X).inv ≫
        HomologicalComplex.tensorHom a b) ≫ c)) ComplexShape.embeddingDownNat) := by
  refine (derivedChainCoordinate_compare_postcompose hres
    (S.map a) (u ≫ S.map b) (τ ≫ S.map c)).trans ?_
  apply congrArg DerivedCategory.Q.map
  apply congrArg (fun f => extendMap f ComplexShape.embeddingDownNat)
  rw [S.map_comp, hunit]
  simp only [Category.assoc]

end HomologicalComplex.TensorNegExtend
