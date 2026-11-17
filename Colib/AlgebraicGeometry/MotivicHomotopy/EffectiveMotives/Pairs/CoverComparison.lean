/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.TransferTriangle
public import Colib.CategoryTheory.Triangulated.SpecifiedCompletion
public import Mathlib.CategoryTheory.Abelian.CommSq
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-!
# Comparing triangulated images of the signed two-open rows

The original signed sum extends through a cofiber of the signed difference.
The extension is uniquely determined after passage to degree-zero transfer
sheaves. This identifies all three maps, including the connecting morphism.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.Scheme

universe u w'

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

section SignedRow

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Preadditive D] [Preadditive E] [HasBinaryBiproducts D] [HasBinaryBiproducts E]
  {J : C ⥤ D} {K : C ⥤ E} (F : D ⥤ E) [F.Additive] [PreservesBinaryBiproducts F]
  (e : J ⋙ F ≅ K) (sq : Square C)

/-- A natural isomorphism on the four corners identifies the signed rows. -/
def mapSignedSquareRowIso :
    ((sq.map J).commSq.shortComplex.map F) ≅ (sq.map K).commSq.shortComplex := by
  refine ShortComplex.isoMk (e.app sq.X₁)
    (F.mapBiprod _ _ ≪≫ biprod.mapIso (e.app sq.X₂) (e.app sq.X₃)) (e.app sq.X₄) ?_ ?_
  · symm
    change F.map (biprod.lift (J.map sq.f₁₂) (-(J.map sq.f₁₃))) ≫
      (F.mapBiprod _ _).hom ≫ biprod.map (e.app sq.X₂).hom (e.app sq.X₃).hom =
    (e.app sq.X₁).hom ≫ biprod.lift (K.map sq.f₁₂) (-(K.map sq.f₁₃))
    rw [← Category.assoc, biprod.map_lift_mapBiprod, F.map_neg]
    apply biprod.hom_ext
    · simpa only [Functor.comp_obj, Functor.comp_map, Iso.app_hom, Category.assoc,
        biprod.map_fst, biprod.lift_fst, biprod.lift_fst_assoc] using e.hom.naturality sq.f₁₂
    · simpa only [Functor.comp_obj, Functor.comp_map, Iso.app_hom, Category.assoc,
        biprod.map_snd, biprod.lift_snd, biprod.lift_snd_assoc, Preadditive.neg_comp,
        Preadditive.comp_neg] using
        congrArg Neg.neg (e.hom.naturality sq.f₁₃)
  · symm
    change F.map (biprod.desc (J.map sq.f₂₄) (J.map sq.f₃₄)) ≫ (e.app sq.X₄).hom =
      ((F.mapBiprod _ _).hom ≫ biprod.map (e.app sq.X₂).hom (e.app sq.X₃).hom) ≫
        biprod.desc (K.map sq.f₂₄) (K.map sq.f₃₄)
    rw [← biprod.mapBiprod_hom_desc F, Category.assoc, Category.assoc]
    congr 1
    apply biprod.hom_ext'
    · simpa only [Functor.comp_obj, Functor.comp_map, Iso.app_hom, biprod.inl_desc,
        biprod.inl_desc_assoc, biprod.inl_map_assoc] using e.hom.naturality sq.f₂₄
    · simpa only [Functor.comp_obj, Functor.comp_map, Iso.app_hom, biprod.inr_desc,
        biprod.inr_desc_assoc, biprod.inr_map_assoc] using e.hom.naturality sq.f₃₄

end SignedRow

/-- The degree-one shift of a single in degree zero has no maps to another such single. -/
theorem derivedMinus_shift_hom_subsingleton_of_single
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {X Y : DerivedCategory.Minus A} {P R : A}
    (a : X.obj ≅ (DerivedCategory.singleFunctor A 0).obj P)
    (b : Y.obj ≅ (DerivedCategory.singleFunctor A 0).obj R) :
    Subsingleton (X⟦(1 : ℤ)⟧ ⟶ Y) := by
  let I := DerivedCategory.Minus.ι (C := A)
  let t := DerivedCategory.TStructure.t (C := A)
  have h (f : X⟦(1 : ℤ)⟧ ⟶ Y) : f = 0 := by
    apply I.map_injective
    rw [I.map_zero]
    let e := (I.commShiftIso (1 : ℤ)).app X
    let : t.IsLE (I.obj X) 0 := t.isLE_of_iso a.symm 0
    let : t.IsLE ((I ⋙ shiftFunctor (DerivedCategory A) (1 : ℤ)).obj X) (-1) :=
      t.isLE_shift (I.obj X) 0 1 (-1) (by decide)
    let : t.IsLE (I.obj (X⟦(1 : ℤ)⟧)) (-1) := t.isLE_of_iso e.symm (-1)
    let : t.IsGE (I.obj Y) 0 := t.isGE_of_iso b.symm 0
    exact t.zero (I.map f) (-1) 0 (by decide)
  exact ⟨fun f g => (h f).trans (h g).symm⟩

/-- A signed row together with its distinguished cofiber and the lift
of its specified sum map. -/
structure SignedRowTriangle {D : Type*} [Category D] [HasZeroObject D] [Preadditive D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (R : ShortComplex D) where
  /-- The chosen cofiber of the first map of the row. -/
  obj₃ : D
  /-- The map from the middle object of the row to the chosen cofiber. -/
  mor₂ : R.X₂ ⟶ obj₃
  /-- The connecting morphism to the shifted first object of the row. -/
  connecting : obj₃ ⟶ R.X₁⟦(1 : ℤ)⟧
  distinguished : Triangle.mk R.f mor₂ connecting ∈ distTriang D
  /-- The augmentation extending `R.g` along `mor₂`. -/
  augmentation : obj₃ ⟶ R.X₃
  augmentation_fac : mor₂ ≫ augmentation = R.g

section Comparison

variable {D : Type*} [Category D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- The chosen cofiber of the signed difference, augmented by the actual signed sum. -/
noncomputable def signedRowTriangle (R : ShortComplex D) : SignedRowTriangle R := by
  let h := distinguished_cocone_triangle R.f
  let Z := h.choose
  let g := h.choose_spec.choose
  let δ := h.choose_spec.choose_spec.choose
  let d := h.choose_spec.choose_spec.choose_spec
  let T := Triangle.mk R.f g δ
  let a := T.yoneda_exact₂ d R.g R.zero
  exact ⟨Z, g, δ, d, a.choose, a.choose_spec.symm⟩

variable (k : Type u) [Field k] [HasDerivedCategory.{w'} (LargeSheaves k)]

local notation "NST(" K ")" => LargeSheaves K
local notation "s(" K ")" => singleTransferSheafMinus K

/-- The canonical abelian structure on the transfer sheaves in the cover row. -/
local instance pairCoverComparisonAbelian : Abelian NST(k) := SheafWithTransfers.abelian k

/-- The prescribed augmentation gives a triangle isomorphism on any exact
image of the signed row that is the original sheaf row placed in degree zero. -/
def signedRowTriangleToTransferIso {R : ShortComplex D} (T : SignedRowTriangle R)
    (F : D ⥤ DerivedCategory.Minus NST(k)) [F.CommShift ℤ] [F.IsTriangulated]
    {L : ShortComplex NST(k)} (h : L.ShortExact) (e : R.map F ≅ L.map (s(k))) :
    F.mapTriangle.obj (Triangle.mk R.f T.mor₂ T.connecting) ≅
      singleTransferSheafTriangle k h := by
  let V := F.mapTriangle.obj (Triangle.mk R.f T.mor₂ T.connecting)
  let W := singleTransferSheafTriangle k h
  have hV : V ∈ distTriang _ := F.map_distinguished _ T.distinguished
  have hW : W ∈ distTriang _ := singleTransferSheafTriangle_distinguished k h
  let I := DerivedCategory.Minus.ι (C := NST(k))
  let a := ShortComplex.π₁.mapIso e
  let b := ShortComplex.π₂.mapIso e
  let c := ShortComplex.π₃.mapIso e
  have ha : I.obj V.obj₁ ≅ (DerivedCategory.singleFunctor NST(k) 0).obj L.X₁ := I.mapIso a
  have h0 : Subsingleton (V.obj₁⟦(1 : ℤ)⟧ ⟶ W.obj₃) :=
    derivedMinus_shift_hom_subsingleton_of_single ha
      (show I.obj W.obj₃ ≅ (DerivedCategory.singleFunctor NST(k) 0).obj L.X₃ from Iso.refl _)
  have h₁ : V.mor₁ ≫ b.hom = a.hom ≫ W.mor₁ := e.hom.comm₁₂.symm
  have h₂ : V.mor₂ ≫ F.map T.augmentation ≫ c.hom = b.hom ≫ W.mor₂ := by
    change F.map T.mor₂ ≫ F.map T.augmentation ≫ c.hom = _
    rw [← F.map_comp_assoc, T.augmentation_fac]
    exact e.hom.comm₂₃.symm
  let f := triangleMorphismOfSubsingleton hV hW h0 a.hom b.hom
    (F.map T.augmentation ≫ c.hom) h₁ h₂
  let : IsIso f.hom₁ := inferInstanceAs (IsIso a.hom)
  let : IsIso f.hom₂ := inferInstanceAs (IsIso b.hom)
  let : IsIso f.hom₃ := isIso₃_of_isIso₁₂ f hV hW inferInstance inferInstance
  let : IsIso f := Triangle.isIso_of_isIsos f inferInstance inferInstance inferInstance
  exact asIso f


variable {R : ShortComplex D} (T : SignedRowTriangle R)
    (F : D ⥤ DerivedCategory.Minus NST(k)) [F.CommShift ℤ] [F.IsTriangulated]
    {L : ShortComplex NST(k)} (h : L.ShortExact) (e : R.map F ≅ L.map (s(k)))

/-- The overlap comparison is the original coefficient comparison. -/
@[simp]
theorem signedRowTriangleToTransferIso_hom₁ :
    (signedRowTriangleToTransferIso k T F h e).hom.hom₁ = e.hom.τ₁ := by
  unfold signedRowTriangleToTransferIso
  rfl

/-- The middle comparison is the original coefficient comparison. -/
@[simp]
theorem signedRowTriangleToTransferIso_hom₂ :
    (signedRowTriangleToTransferIso k T F h e).hom.hom₂ = e.hom.τ₂ := by
  unfold signedRowTriangleToTransferIso
  rfl

/-- The map from the chosen cofiber is its specified augmentation. -/
@[simp]
theorem signedRowTriangleToTransferIso_hom₃ :
    (signedRowTriangleToTransferIso k T F h e).hom.hom₃ =
      F.map T.augmentation ≫ e.hom.τ₃ := by
  unfold signedRowTriangleToTransferIso
  rfl

end Comparison

end AlgebraicGeometry.MotivicHomotopy
