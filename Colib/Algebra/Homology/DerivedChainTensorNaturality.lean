/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.TensorNegExtendNaturality
public import StacksFrontier.Homology.KFlat.BifunctorToTotalComplex

/-! # Naturality of the original derived-to-chain tensor comparison

The native derived tensor maps, `toTensor`, and negative-extension tensor
comparison form one square. No K-flatness or invertibility of its inputs or
maps is assumed, and no new pairing is defined.
-/

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

/-- Naturality of the native comparison from the original derived tensor to the
localization of the original chain tensor. The target `toTensor` need not be an
isomorphism. -/
theorem derivedChainTensor_naturality {K K' L L' : ChainComplex A ℕ}
    (a : K ⟶ K') (b : L ⟶ L') :
    ((derivedBifunctor (curriedTensor A)).map
      (DerivedCategory.Q.map (extendMap a ComplexShape.embeddingDownNat))).app
        (DerivedCategory.Q.obj (negExtend L)) ≫
      ((derivedBifunctor (curriedTensor A)).obj
        (DerivedCategory.Q.obj (negExtend K'))).map
          (DerivedCategory.Q.map (extendMap b ComplexShape.embeddingDownNat)) ≫
      toTensor (curriedTensor A) hres (negExtend K') (negExtend L') ≫
      DerivedCategory.Q.map (tensorNegExtendFullIso K' L').hom =
    toTensor (curriedTensor A) hres (negExtend K) (negExtend L) ≫
      DerivedCategory.Q.map (tensorNegExtendFullIso K L).hom ≫
      DerivedCategory.Q.map
        (extendMap (HomologicalComplex.tensorHom a b) ComplexShape.embeddingDownNat) := by
  have ht := toTensor_naturality (curriedTensor A) hres
    (extendMap a ComplexShape.embeddingDownNat)
    (extendMap b ComplexShape.embeddingDownNat)
  have he := congrArg DerivedCategory.Q.map (tensorNegExtendFullIso_naturality a b)
  calc
    _ = toTensor (curriedTensor A) hres (negExtend K) (negExtend L) ≫
        DerivedCategory.Q.map
          (HomologicalComplex.tensorHom (extendMap a ComplexShape.embeddingDownNat)
            (extendMap b ComplexShape.embeddingDownNat)) ≫
        DerivedCategory.Q.map (tensorNegExtendFullIso K' L').hom := by
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ DerivedCategory.Q.map
          (tensorNegExtendFullIso K' L').hom) ht
    _ = _ := by
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun f => toTensor (curriedTensor A) hres
          (negExtend K) (negExtend L) ≫ f) he

end HomologicalComplex.TensorNegExtend
