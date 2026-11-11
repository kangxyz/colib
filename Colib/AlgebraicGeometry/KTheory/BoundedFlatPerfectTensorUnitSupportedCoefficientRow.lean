/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitCoefficientRow
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitSupportHomotopy

/-!
# The actual first coefficient tensor row inside supported complexes

Every entry is the original coefficient tensor complex, proved acyclic on the given open.
The row predicates are established inside the original supported Waldhausen category by
its actual tensor-zero isomorphisms and supported one-step row.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.QuotientRows
open AlgebraicGeometry.RingedSpace
open scoped Simplicial ZeroObject
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {U X : Scheme.{u}} (ι : U ⟶ X) [IsOpenImmersion ι]

/-- Each original tensor entry remains in the bounded-flat perfect category. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientRow.lean:31"
  "adaptation" "Original supported tensor-zero row, mixed exactness and coefficient square."]
theorem complexTensorUnitRows_supported (K : (boundedAboveFlatPerfectSupported ι).FullSubcategory)
    (p : Interval ⦋1⦌) :
    boundedAboveFlatPerfectSupported ι (((complexTensorUnitRows X).obj K.obj).obj p) := by
  rcases p with ⟨⟨i, j⟩, hij⟩
  fin_cases i <;> fin_cases j
  · exact ⟨boundedAboveFlatPerfectComplex_of_isZero
      (complexTensorLeft_isZero_of_coefficient (isZero_zero _) K.obj),
      HomologicalComplex.acyclic_of_isZero _ (((restrictFunctor ι).mapHomologicalComplex
      (.up ℤ)).map_isZero
        (complexTensorLeft_isZero_of_coefficient (isZero_zero _) K.obj))⟩
  · exact ((boundedAboveFlatPerfectSupportedTensorUnit ι).obj K).property
  · exact False.elim (Nat.not_succ_le_zero 0 hij)
  · exact ⟨boundedAboveFlatPerfectComplex_of_isZero
      (complexTensorLeft_isZero_of_coefficient (isZero_zero _) K.obj),
      HomologicalComplex.acyclic_of_isZero _ (((restrictFunctor ι).mapHomologicalComplex
      (.up ℤ)).map_isZero
        (complexTensorLeft_isZero_of_coefficient (isZero_zero _) K.obj))⟩

/-- Lift the actual tensor diagrams, without replacing either tensor-zero endpoint. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientRow.lean:48"
  "adaptation" "Original supported tensor-zero row, mixed exactness and coefficient square."]
def boundedAboveFlatPerfectSupportedTensorUnitRows :
    (boundedAboveFlatPerfectSupported ι).FullSubcategory ⥤
      (Interval ⦋1⦌ ⥤ (boundedAboveFlatPerfectSupported ι).FullSubcategory) where
  obj K := (boundedAboveFlatPerfectSupported ι).lift ((complexTensorUnitRows X).obj K.obj)
    (complexTensorUnitRows_supported ι K)
  map f :=
    { app p := (boundedAboveFlatPerfectSupported ι).homMk
        (((complexTensorUnitRows X).map f.hom).app p)
      naturality p q g := by
        apply (boundedAboveFlatPerfectSupported ι).ι.map_injective
        exact ((complexTensorUnitRows X).map f.hom).naturality g }
  map_id K := by
    apply NatTrans.ext
    funext p
    apply (boundedAboveFlatPerfectSupported ι).ι.map_injective
    exact NatTrans.congr_app ((complexTensorUnitRows X).map_id K.obj) p
  map_comp f g := by
    apply NatTrans.ext
    funext p
    apply (boundedAboveFlatPerfectSupported ι).ι.map_injective
    exact NatTrans.congr_app ((complexTensorUnitRows X).map_comp f.hom g.hom) p

/-- Both diagonal entries are actual zero objects, as proved from their original tensor terms. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientRow.lean:70"
  "adaptation" "Original supported tensor-zero row, mixed exactness and coefficient square."]
theorem boundedAboveFlatPerfectSupportedTensorUnitRows_zero
    (K : (boundedAboveFlatPerfectSupported ι).FullSubcategory)
    (i : Fin 2) :
    IsZero (((boundedAboveFlatPerfectSupportedTensorUnitRows ι).obj K).obj
      (interval i i le_rfl)) := by
  rw [IsZero.iff_id_eq_zero]
  apply (boundedAboveFlatPerfectSupported ι).ι.map_injective
  fin_cases i <;>
    exact (complexTensorLeft_isZero_of_coefficient (isZero_zero _) K.obj).eq_of_src _ _

/-- Original tensor-zero isomorphisms and the identity at the actual tensor-unit entry. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientRow.lean:80"
  "adaptation" "Original supported tensor-zero row, mixed exactness and coefficient square."]
def supportedTensorUnitRowIsoAt (K : (boundedAboveFlatPerfectSupported ι).FullSubcategory)
    (p : Interval ⦋1⦌) :
    ((boundedAboveFlatPerfectSupportedTensorUnitRows ι).obj K).obj p ≅
      (oneDiagram (boundedAboveFlatPerfectSupportedWaldhausen ι)
        ((boundedAboveFlatPerfectSupportedTensorUnit ι).obj K)).obj p := by
  rcases p with ⟨⟨i, j⟩, hij⟩
  change Fin 2 at i j
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero =>
      exact (boundedAboveFlatPerfectSupportedTensorUnitRows_zero ι K 0).iso
        (boundedAboveFlatPerfectSupportedWaldhausen ι).isZero
    | succ j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact Iso.refl _
  | succ i =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    cases j using Fin.cases with
    | zero => exact False.elim (Nat.not_succ_le_zero 0 hij)
    | succ j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact (boundedAboveFlatPerfectSupportedTensorUnitRows_zero ι K 1).iso
        (boundedAboveFlatPerfectSupportedWaldhausen ι).isZero

/-- All original coefficient arrows commute with the actual endpoint-zero isomorphisms. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientRow.lea\
    n:109"
  "adaptation" "Original supported tensor-zero row, mixed exactness and coefficient square."]
theorem supportedTensorUnitRowIsoAt_naturality
    (K : (boundedAboveFlatPerfectSupported ι).FullSubcategory)
    {p q : Interval ⦋1⦌} (f : p ⟶ q) :
    ((boundedAboveFlatPerfectSupportedTensorUnitRows ι).obj K).map f ≫
        (supportedTensorUnitRowIsoAt ι K q).hom =
      (supportedTensorUnitRowIsoAt ι K p).hom ≫
        (oneDiagram (boundedAboveFlatPerfectSupportedWaldhausen ι)
          ((boundedAboveFlatPerfectSupportedTensorUnit ι).obj K)).map f := by
  rcases p with ⟨⟨i, j⟩, hij⟩
  rcases q with ⟨⟨k, l⟩, hkl⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> solve
  | exact False.elim (Nat.not_succ_le_zero 0 hij)
  | exact False.elim (Nat.not_succ_le_zero 0 hkl)
  | exact (boundedAboveFlatPerfectSupportedTensorUnitRows_zero ι K 0).eq_of_src _ _
  | exact (boundedAboveFlatPerfectSupportedWaldhausen ι).isZero.eq_of_tgt _ _
  | have hf : f = 𝟙 _ := Subsingleton.elim _ _
    subst f
    simp

/-- The entire independently tensored first row is isomorphic to the original one-step row. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientRow.lea\
    n:130"
  "adaptation" "Original supported tensor-zero row, mixed exactness and coefficient square."]
def supportedTensorUnitRowDiagramIso (K : (boundedAboveFlatPerfectSupported ι).FullSubcategory) :
    (boundedAboveFlatPerfectSupportedTensorUnitRows ι).obj K ≅
      oneDiagram (boundedAboveFlatPerfectSupportedWaldhausen ι)
        ((boundedAboveFlatPerfectSupportedTensorUnit ι).obj K) :=
  NatIso.ofComponents (supportedTensorUnitRowIsoAt ι K) (supportedTensorUnitRowIsoAt_naturality ι K)

/-- The actual first tensor row has genuine zero, cofibration and quotient-pushout conditions. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientRow.lea\
    n:137"
  "adaptation" "Original supported tensor-zero row, mixed exactness and coefficient square."]
theorem boundedAboveFlatPerfectSupportedTensorUnitRows_isRow
    (K : (boundedAboveFlatPerfectSupported ι).FullSubcategory) :
    IsRow (boundedAboveFlatPerfectSupportedWaldhausen ι)
      ((boundedAboveFlatPerfectSupportedTensorUnitRows ι).obj K) :=
  (oneDiagram_isRow (boundedAboveFlatPerfectSupportedWaldhausen ι) _).of_iso _
    (supportedTensorUnitRowDiagramIso ι K).symm

end AlgebraicGeometry.Scheme.Modules
