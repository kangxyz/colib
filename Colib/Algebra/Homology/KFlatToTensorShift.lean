/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.KFlatToTensorNatTrans
public import Colib.Algebra.Homology.KFlatComparisonShift
public import Colib.CategoryTheory.Shift.DetectOnResolutions
public import StacksFrontier.Homology.KFlat.BifunctorOneSidedComparison

/-! # The original derived-to-total morphism as a two-variable transformation

The components are exactly native `KFlatBifunctor.toTensor`, with no alteration
of resolutions, derived category model, or tensor object.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.KFlatBifunctor

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K : CochainComplex A ℤ) (L : CochainComplex B ℤ),
    HomologicalComplex.HasMapBifunctor K L F (.up ℤ)]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]
  [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)]
  (hres : ∀ G : CochainComplex B ℤ, ∃ (P : CochainComplex B ℤ) (f : P ⟶ G),
    KFlat F P ∧ QuasiIso f)

/-- The native canonical morphism as a transformation in its first variable. -/
def nativeToTensorFirst (L : CochainComplex B ℤ) :
    DerivedCategory.Q ⋙ (derivedBifunctor F).flip.obj (DerivedCategory.Q.obj L) ⟶
      (totalBifunctor F).flip.obj L ⋙ DerivedCategory.Q where
  app K := toTensor F hres K L
  naturality {K K'} f := by
    simpa using toTensor_naturality' F hres f (𝟙 L)

/-- If the second factor is K-flat, the actual canonical map commutes with
shifts in the arbitrary first factor. Only the source inverts the resolving maps. -/
theorem nativeToTensorFirst_commShift_of_kFlat
    (resL : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
      KFlatLeft F P ∧ QuasiIso f)
    (L : CochainComplex B ℤ) (hL : KFlat F L) :
    NatTrans.CommShift (nativeToTensorFirst F hres L) ℤ := by
  have heq : Functor.whiskerLeft (kFlatComplexesLeft F).ι
      (nativeToTensorFirst F hres L) =
      (Functor.associator (kFlatComplexesLeft F).ι DerivedCategory.Q
        ((derivedBifunctor F).flip.obj (DerivedCategory.Q.obj L))).inv ≫
          (comparisonFirst F L hL).hom := by
    ext K
    change toTensor F hres K.1 L = 𝟙 _ ≫ (comparisonFirst F L hL).hom.app K
    rw [Category.id_comp]
    rw [comparisonFirst_hom_app, toTensor_eq_comparisonRight F hres K.1 hL,
      comparisonRight_hom_eq_comparison_hom F K.1 L K.2 hL]
  have : NatTrans.CommShift (Functor.whiskerLeft (kFlatComplexesLeft F).ι
      (nativeToTensorFirst F hres L)) ℤ := by
    rw [heq]
    let := comparisonFirst_commShift F L hL
    infer_instance
  apply NatTrans.commShift_of_resolving_whiskerLeft (kFlatComplexesLeft F).ι
    (nativeToTensorFirst F hres L)
  intro K n
  obtain ⟨P, f, hP, hf⟩ := resL K
  let := hf
  refine ⟨⟨P, hP⟩, f, ?_⟩
  change Epi (((derivedBifunctor F).flip.obj (DerivedCategory.Q.obj L)).map
    (DerivedCategory.Q.map ((CategoryTheory.shiftFunctor (CochainComplex A ℤ) n).map f)))
  infer_instance

/-- The native canonical morphism commutes with shifts in the first variable
for every second factor, by a K-flat resolution of that factor. -/
theorem nativeToTensorFirst_commShift
    (resL : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
      KFlatLeft F P ∧ QuasiIso f)
    (L : CochainComplex B ℤ) :
    NatTrans.CommShift (nativeToTensorFirst F hres L) ℤ := by
  obtain ⟨N, q, hN, hq⟩ := hres L
  let := hq
  let S := Functor.whiskerLeft DerivedCategory.Q
    ((derivedBifunctor F).flip.map (DerivedCategory.Q.map q))
  let T := Functor.whiskerRight ((totalBifunctor F).flip.map q) DerivedCategory.Q
  have hS : IsIso S := by dsimp [S]; infer_instance
  have hs : NatTrans.CommShift S ℤ := by dsimp [S]; infer_instance
  have hi := NatTrans.CommShift.of_isIso S ℤ
  have ht : NatTrans.CommShift T ℤ := by dsimp [T, totalBifunctor]; infer_instance
  have hn := nativeToTensorFirst_commShift_of_kFlat F hres resL N hN
  have heq : nativeToTensorFirst F hres L =
      inv S ≫ nativeToTensorFirst F hres N ≫ T := by
    rw [← cancel_epi S, IsIso.hom_inv_id_assoc]
    ext K
    simpa [S, T, nativeToTensorFirst] using
      toTensor_naturality' F hres (𝟙 K) q
  rw [heq]
  infer_instance

/-- The native canonical morphism as a transformation in its second variable. -/
def nativeToTensorSecond (K : CochainComplex A ℤ) :
    DerivedCategory.Q ⋙ (derivedBifunctor F).obj (DerivedCategory.Q.obj K) ⟶
      (totalBifunctor F).obj K ⋙ DerivedCategory.Q where
  app L := toTensor F hres K L
  naturality {L L'} g := by
    simpa using toTensor_naturality' F hres (𝟙 K) g

/-- At a left K-flat first factor the original map commutes with second-variable shifts. -/
theorem nativeToTensorSecond_commShift_of_kFlatLeft
    (K : CochainComplex A ℤ) (hK : KFlatLeft F K) :
    NatTrans.CommShift (nativeToTensorSecond F hres K) ℤ := by
  have heq : Functor.whiskerLeft (kFlatComplexes F).ι
      (nativeToTensorSecond F hres K) =
      (Functor.associator (kFlatComplexes F).ι DerivedCategory.Q
        ((derivedBifunctor F).obj (DerivedCategory.Q.obj K))).inv ≫
          (comparisonSecond F K hK).hom := by
    ext L
    change toTensor F hres K L.1 = 𝟙 _ ≫ (comparisonSecond F K hK).hom.app L
    rw [Category.id_comp, comparisonSecond_hom_app,
      toTensor_eq_comparisonRight F hres K L.2,
      comparisonRight_hom_eq_comparison_hom F K L.1 hK L.2]
  have : NatTrans.CommShift (Functor.whiskerLeft (kFlatComplexes F).ι
      (nativeToTensorSecond F hres K)) ℤ := by
    rw [heq]
    let := comparisonSecond_commShift F K hK
    infer_instance
  apply NatTrans.commShift_of_resolving_whiskerLeft (kFlatComplexes F).ι
    (nativeToTensorSecond F hres K)
  intro L n
  obtain ⟨P, f, hP, hf⟩ := hres L
  let := hf
  refine ⟨⟨P, hP⟩, f, ?_⟩
  change Epi (((derivedBifunctor F).obj (DerivedCategory.Q.obj K)).map
    (DerivedCategory.Q.map ((CategoryTheory.shiftFunctor (CochainComplex B ℤ) n).map f)))
  infer_instance

/-- The canonical map commutes with second-variable shifts for arbitrary complexes. -/
theorem nativeToTensorSecond_commShift
    (resL : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
      KFlatLeft F P ∧ QuasiIso f)
    (K : CochainComplex A ℤ) :
    NatTrans.CommShift (nativeToTensorSecond F hres K) ℤ := by
  obtain ⟨P, q, hP, hq⟩ := resL K
  let := hq
  let S := Functor.whiskerLeft DerivedCategory.Q
    ((derivedBifunctor F).map (DerivedCategory.Q.map q))
  let T := Functor.whiskerRight ((totalBifunctor F).map q) DerivedCategory.Q
  have hS : IsIso S := by dsimp [S]; infer_instance
  have hs : NatTrans.CommShift S ℤ := by dsimp [S]; infer_instance
  have hi := NatTrans.CommShift.of_isIso S ℤ
  have ht : NatTrans.CommShift T ℤ := by dsimp [T, totalBifunctor]; infer_instance
  have hn := nativeToTensorSecond_commShift_of_kFlatLeft F hres P hP
  have heq : nativeToTensorSecond F hres K =
      inv S ≫ nativeToTensorSecond F hres P ≫ T := by
    rw [← cancel_epi S, IsIso.hom_inv_id_assoc]
    ext L
    simpa [S, T, nativeToTensorSecond] using toTensor_naturality' F hres q (𝟙 L)
  rw [heq]
  infer_instance

end CochainComplex.KFlatBifunctor
