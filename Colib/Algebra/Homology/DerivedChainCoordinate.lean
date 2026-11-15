/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Algebra.Homology.DerivedUnitCoordinate
public import Colib.Algebra.Homology.TensorNegExtendCoordinate
/-! # Actual chain coordinate maps into the original derived tensor bifunctor -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
open CochainComplex.KFlatBifunctor
namespace HomologicalComplex.TensorNegExtend
variable {A : Type*} [Category A] [Abelian A] [MonoidalCategory A]
  [MonoidalPreadditive A] [HasCoproducts.{0} A] [HasDerivedCategory A]
  [(kFlatQLeft (curriedTensor A)).IsLocalization (kFlatQuasiIsoLeft (curriedTensor A))]
  [(kFlatQ (curriedTensor A)).IsLocalization (kFlatQuasiIso (curriedTensor A))]
  (hres : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
    KFlat (curriedTensor A) P ∧ QuasiIso f)

/-- The native derived tensor of a projection and a genuine chain unit coordinate.
The original target bifunctor and unit comparison are retained. -/
def derivedChainCoordinate {X K L : ChainComplex A ℕ} (a : X ⟶ K)
    (b : HomologicalComplex.tensorUnit A (.down ℕ) ⟶ L) :
    DerivedCategory.Q.obj (negExtend X) ⟶
      ((derivedBifunctor (curriedTensor A)).obj (DerivedCategory.Q.obj (negExtend K))).obj
        (DerivedCategory.Q.obj (negExtend L)) :=
  letI := isIso_toTensor_nativeUnit hres (negExtend X)
  DerivedCategory.Q.map (HomologicalComplex.rightUnitor (negExtend X)).inv ≫
    inv (toTensor (curriedTensor A) hres (negExtend X)
      (HomologicalComplex.tensorUnit A (.up ℤ))) ≫
    ((derivedBifunctor (curriedTensor A)).map
      (DerivedCategory.Q.map (extendMap a ComplexShape.embeddingDownNat))).app
        (DerivedCategory.Q.obj (HomologicalComplex.tensorUnit A (.up ℤ))) ≫
    ((derivedBifunctor (curriedTensor A)).obj (DerivedCategory.Q.obj (negExtend K))).map
      (DerivedCategory.Q.map (tensorNegExtendUnitIso.inv ≫
        extendMap b ComplexShape.embeddingDownNat))

/-- The actual native comparisons recover extension/localization of the original
chain insertion. No invertibility at the target pair is assumed. -/
theorem derivedChainCoordinate_compare {X K L : ChainComplex A ℕ} (a : X ⟶ K)
    (b : HomologicalComplex.tensorUnit A (.down ℕ) ⟶ L) :
    derivedChainCoordinate hres a b ≫
      toTensor (curriedTensor A) hres (negExtend K) (negExtend L) ≫
      DerivedCategory.Q.map (tensorNegExtendFullIso K L).hom =
    DerivedCategory.Q.map (extendMap ((HomologicalComplex.rightUnitor X).inv ≫
      HomologicalComplex.tensorHom a b) ComplexShape.embeddingDownNat) := by
  have ht := toTensor_unitCoordinate hres (extendMap a ComplexShape.embeddingDownNat)
    (tensorNegExtendUnitIso.inv ≫ extendMap b ComplexShape.embeddingDownNat)
  have he := congrArg DerivedCategory.Q.map (tensorNegExtendFullIso_unitCoordinate a b)
  calc
    _ = DerivedCategory.Q.map ((HomologicalComplex.rightUnitor (negExtend X)).inv ≫
        HomologicalComplex.tensorHom (extendMap a ComplexShape.embeddingDownNat)
          (tensorNegExtendUnitIso.inv ≫ extendMap b ComplexShape.embeddingDownNat)) ≫
        DerivedCategory.Q.map (tensorNegExtendFullIso K L).hom := by
      simpa only [derivedChainCoordinate, Category.assoc] using
        congrArg (fun f => f ≫ DerivedCategory.Q.map (tensorNegExtendFullIso K L).hom) ht
    _ = _ := by simpa only [Functor.map_comp, Category.assoc] using he.symm

/-- Retaining any original target map after the native tensor comparison recovers
exactly the original postcomposed chain insertion. -/
theorem derivedChainCoordinate_compare_postcompose {X K L Z : ChainComplex A ℕ}
    (a : X ⟶ K) (b : HomologicalComplex.tensorUnit A (.down ℕ) ⟶ L)
    (c : HomologicalComplex.tensorObj K L ⟶ Z) :
    derivedChainCoordinate hres a b ≫
      toTensor (curriedTensor A) hres (negExtend K) (negExtend L) ≫
      DerivedCategory.Q.map ((tensorNegExtendFullIso K L).hom ≫
        extendMap c ComplexShape.embeddingDownNat) =
    DerivedCategory.Q.map (extendMap
      (((HomologicalComplex.rightUnitor X).inv ≫ HomologicalComplex.tensorHom a b) ≫ c)
      ComplexShape.embeddingDownNat) := by
  simpa only [Functor.map_comp, extendMap_comp, Category.assoc] using
    congrArg (fun f => f ≫ DerivedCategory.Q.map (extendMap c ComplexShape.embeddingDownNat))
      (derivedChainCoordinate_compare hres a b)

end HomologicalComplex.TensorNegExtend
