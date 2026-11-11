/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.Modules.ComplexTensorZero
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectTensorUnitEdge
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitHomotopy
public import Colib.CategoryTheory.Waldhausen.Rows.OneRow
public import Colib.CategoryTheory.Waldhausen.Rows.Isomorphism

/-!
# The actual first coefficient tensor row

The coefficient interval diagram is the actual module row `0, O, 0`. Applying the genuine
coefficient tensor functor and evaluating on the second input gives the literal objects
`0 ⊗ K, O ⊗ K, 0 ⊗ K`. Their actual zero isomorphisms identify this whole diagram with the
original one-step quotient row on `O ⊗ K`, before any quotient-row property is transported.
The coefficient row has not yet been identified with its degree-zero Waldhausen K-one class.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.RingedSpace
open MonoidalCategory
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.QuotientRows
open scoped Simplicial ZeroObject
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The native sheaf-of-modules monoidal structure on the scheme. -/
local instance tensorUnitCoefficientRowMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Stacks.SheafOfModules.OnSpace.monoidal X.toRingedSpace
local instance tensorUnitCoefficientRowPreadditive (X : Scheme.{u}) : MonoidalPreadditive
  X.Modules :=
  Stacks.SheafOfModules.OnSpace.monoidalPreadditive X.toRingedSpace

/-- The original module coefficient row has the literal objects zero, structure module, zero. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitCoefficientRow.lean:35"
  "adaptation" "Original tensor-zero objects and unchanged whole quotient-row proof."]
def tensorUnitCoefficientRow (X : Scheme.{u}) : Interval ⦋1⦌ ⥤ X.Modules :=
  oneIndex ⋙ ComposableArrows.mk₂
    (0 : (0 : X.Modules) ⟶ 𝟙_ X.Modules)
    (0 : 𝟙_ X.Modules ⟶ (0 : X.Modules))

/-- Apply genuine tensor to the coefficient row, then evaluate on each independent complex. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitCoefficientRow.lean:41"
  "adaptation" "Original tensor-zero objects and unchanged whole quotient-row proof."]
def complexTensorUnitRows (X : Scheme.{u}) :
    CochainComplex X.Modules ℤ ⥤ (Interval ⦋1⦌ ⥤ CochainComplex X.Modules ℤ) :=
  (tensorUnitCoefficientRow X ⋙ complexTensorCoefficientFunctor X).flip

/-- The middle coefficient is the original tensor-unit object. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitCoefficientRow.lean:46"
  "adaptation" "Original tensor-zero objects and unchanged whole quotient-row proof."]
theorem complexTensorUnitRows_whole (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ) :
    ((complexTensorUnitRows X).obj K).obj (interval 0 1 (by decide)) =
      ((MonoidalCategory.tensorLeft (𝟙_ X.Modules)).mapHomologicalComplex (.up ℤ)).obj K := rfl

/-- Each original tensor entry remains in the bounded-flat perfect category. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitCoefficientRow.lean:51"
  "adaptation" "Original tensor-zero objects and unchanged whole quotient-row proof."]
theorem complexTensorUnitRows_boundedFlat (X : Scheme.{u}) (K : (boundedAboveFlatPerfectComplex
  X.toRingedSpace).FullSubcategory)
    (p : Interval ⦋1⦌) :
    boundedAboveFlatPerfectComplex X.toRingedSpace (((complexTensorUnitRows X).obj K.obj).obj p)
      := by
  rcases p with ⟨⟨i, j⟩, hij⟩
  fin_cases i <;> fin_cases j
  · exact boundedAboveFlatPerfectComplex_of_isZero
      (complexTensorLeft_isZero_of_coefficient (isZero_zero _) K.obj)
  · exact ((boundedAboveFlatPerfectTensorUnit X).obj K).property
  · exact False.elim (Nat.not_succ_le_zero 0 hij)
  · exact boundedAboveFlatPerfectComplex_of_isZero
      (complexTensorLeft_isZero_of_coefficient (isZero_zero _) K.obj)

/-- Lift the actual tensor diagrams, without replacing either tensor-zero endpoint. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitCoefficientRow.lean:64"
  "adaptation" "Original tensor-zero objects and unchanged whole quotient-row proof."]
def boundedAboveFlatPerfectTensorUnitRows (X : Scheme.{u}) :
    (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory ⥤ (Interval ⦋1⦌ ⥤
      (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory) where
  obj K := (boundedAboveFlatPerfectComplex X.toRingedSpace).lift ((complexTensorUnitRows X).obj
    K.obj)
    (complexTensorUnitRows_boundedFlat X K)
  map f :=
    { app p := (boundedAboveFlatPerfectComplex X.toRingedSpace).homMk (((complexTensorUnitRows
      X).map f.hom).app p)
      naturality p q g := by
        apply (boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map_injective
        exact ((complexTensorUnitRows X).map f.hom).naturality g }
  map_id K := by
    apply NatTrans.ext
    funext p
    apply (boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map_injective
    exact NatTrans.congr_app ((complexTensorUnitRows X).map_id K.obj) p
  map_comp f g := by
    apply NatTrans.ext
    funext p
    apply (boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map_injective
    exact NatTrans.congr_app ((complexTensorUnitRows X).map_comp f.hom g.hom) p

/-- Both diagonal entries are actual zero objects, as proved from their original tensor terms. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitCoefficientRow.lean:85"
  "adaptation" "Original tensor-zero objects and unchanged whole quotient-row proof."]
theorem boundedAboveFlatPerfectTensorUnitRows_zero (X : Scheme.{u}) (K :
  (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory)
    (i : Fin 2) :
    IsZero (((boundedAboveFlatPerfectTensorUnitRows X).obj K).obj (interval i i le_rfl)) := by
  rw [IsZero.iff_id_eq_zero]
  apply (boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map_injective
  fin_cases i <;>
    exact (complexTensorLeft_isZero_of_coefficient (isZero_zero _) K.obj).eq_of_src _ _

/-- Original tensor-zero isomorphisms and the identity at the actual tensor-unit entry. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitCoefficientRow.lean:94"
  "adaptation" "Original tensor-zero objects and unchanged whole quotient-row proof."]
def tensorUnitRowIsoAt (X : Scheme.{u}) (K : (boundedAboveFlatPerfectComplex
  X.toRingedSpace).FullSubcategory) (p : Interval ⦋1⦌) :
    ((boundedAboveFlatPerfectTensorUnitRows X).obj K).obj p ≅
      (oneDiagram (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
        ((boundedAboveFlatPerfectTensorUnit X).obj K)).obj p := by
  rcases p with ⟨⟨i, j⟩, hij⟩
  change Fin 2 at i j
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero =>
      exact (boundedAboveFlatPerfectTensorUnitRows_zero X K 0).iso
        (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).isZero
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
      exact (boundedAboveFlatPerfectTensorUnitRows_zero X K 1).iso
        (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).isZero

/-- All original coefficient arrows commute with the actual endpoint-zero isomorphisms. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitCoefficientRow.lean:122"
  "adaptation" "Original tensor-zero objects and unchanged whole quotient-row proof."]
theorem tensorUnitRowIsoAt_naturality (X : Scheme.{u}) (K : (boundedAboveFlatPerfectComplex
  X.toRingedSpace).FullSubcategory)
    {p q : Interval ⦋1⦌} (f : p ⟶ q) :
    ((boundedAboveFlatPerfectTensorUnitRows X).obj K).map f ≫ (tensorUnitRowIsoAt X K q).hom =
      (tensorUnitRowIsoAt X K p).hom ≫
        (oneDiagram (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
          ((boundedAboveFlatPerfectTensorUnit X).obj K)).map f := by
  rcases p with ⟨⟨i, j⟩, hij⟩
  rcases q with ⟨⟨k, l⟩, hkl⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> solve
  | exact False.elim (Nat.not_succ_le_zero 0 hij)
  | exact False.elim (Nat.not_succ_le_zero 0 hkl)
  | exact (boundedAboveFlatPerfectTensorUnitRows_zero X K 0).eq_of_src _ _
  | exact (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).isZero.eq_of_tgt _ _
  | have hf : f = 𝟙 _ := Subsingleton.elim _ _
    subst f
    simp

/-- The entire independently tensored first row is isomorphic to the original one-step row. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitCoefficientRow.lean:141"
  "adaptation" "Original tensor-zero objects and unchanged whole quotient-row proof."]
def tensorUnitRowDiagramIso (X : Scheme.{u}) (K : (boundedAboveFlatPerfectComplex
  X.toRingedSpace).FullSubcategory) :
    (boundedAboveFlatPerfectTensorUnitRows X).obj K ≅
      oneDiagram (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
        ((boundedAboveFlatPerfectTensorUnit X).obj K) :=
  NatIso.ofComponents (tensorUnitRowIsoAt X K) (tensorUnitRowIsoAt_naturality X K)

/-- The actual first tensor row has genuine zero, cofibration and quotient-pushout conditions. -/
@[colib_ref "quillen" "Quillen c561118b: TensorUnitCoefficientRow.lean:147"
  "adaptation" "Original tensor-zero objects and unchanged whole quotient-row proof."]
theorem boundedAboveFlatPerfectTensorUnitRows_isRow (X : Scheme.{u}) (K :
  (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory) :
    IsRow (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
      ((boundedAboveFlatPerfectTensorUnitRows X).obj K) :=
  (oneDiagram_isRow (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) _).of_iso _
    (tensorUnitRowDiagramIso X K).symm

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0544"] boundedAboveFlatPerfectTensorUnitRows_isRow

end AlgebraicGeometry.Scheme.Modules
