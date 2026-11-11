/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Localization.Representability
public import Colib.CategoryTheory.Sites.Simplicial.IntervalLocalization
public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Localization.Composition

/-!
# Morphisms into interval-local objects

The original stalkwise localization factors through the interval localization.
For an interval-local target, the induced map on morphisms is a bijection:
its stalkwise Yoneda functor inverts the actual image of the interval class.
The resulting equivalence retains the original localization maps and
precomposition. No local replacement or homotopy-pushout theorem is used.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable (C : Type u) [Category.{v} C] (J : GrothendieckTopology C)
  (I : Cᵒᵖ ⥤ SSet.{w})

local notation "Qₛ" => toStalkwiseHomotopyCategory C J
local notation "Qᵢ" => toIntervalHomotopyCategory C J I
local notation "Wₛ" => stalkwiseWeakEquivalences C J
local notation "Wᵢ" => intervalWeakEquivalences C J I

/-- The functor from the selected stalkwise category to the selected interval category. -/
def stalkwiseToIntervalHomotopyCategory :
    StalkwiseHomotopyCategory.{w} C J ⥤ IntervalHomotopyCategory C J I :=
  Localization.lift (W := Wₛ) Qᵢ
    (fun _ _ f hf ↦ (Wᵢ).Q_inverts f
      (stalkwiseWeakEquivalences_le_intervalWeakEquivalences C J I f hf)) Qₛ

local notation "L" => stalkwiseToIntervalHomotopyCategory C J I

instance : Localization.Lifting Qₛ Wₛ Qᵢ L := by
  unfold stalkwiseToIntervalHomotopyCategory
  exact Localization.liftingLift (W := Wₛ) _ _ _

/-- The factorization retains the actual original localization functors. -/
def stalkwiseToIntervalHomotopyCategoryCompIso : Qₛ ⋙ L ≅ Qᵢ :=
  Localization.Lifting.iso Qₛ Wₛ Qᵢ L

/-- The intermediate functor localizes at the actual image of the interval class. -/
instance stalkwiseToIntervalHomotopyCategory_isLocalization :
    (L).IsLocalization ((Wᵢ).map Qₛ) := by
  let : (Qₛ ⋙ L).IsLocalization Wᵢ :=
    Functor.IsLocalization.of_iso (W := Wᵢ)
      (stalkwiseToIntervalHomotopyCategoryCompIso C J I).symm
  exact Functor.IsLocalization.of_comp
    (L₁ := Qₛ) (W₁ := Wₛ) (L₂ := L) (W₂ := (Wᵢ).map Qₛ) (W₃ := Wᵢ)
    (stalkwiseWeakEquivalences_le_intervalWeakEquivalences C J I) rfl

/-- The actual stalkwise Yoneda functor of an interval-local object inverts
the image of every interval weak equivalence. -/
theorem isInvertedBy_intervalImage_yoneda
    (Y : StalkwiseHomotopyCategory.{w} C J) (hY : IsIntervalLocal C J I Y) :
    ((Wᵢ).map Qₛ).op.IsInvertedBy (CategoryTheory.yoneda.obj Y) := by
  have h : (Wᵢ).IsInvertedBy (Qₛ ⋙ (CategoryTheory.yoneda.obj Y).rightOp) := by
    intro X X' f hf
    let : IsIso ((CategoryTheory.yoneda.obj Y).map ((Qₛ).map f).op) :=
      (CategoryTheory.isIso_iff_bijective _).2 (hf Y hY)
    change IsIso (((CategoryTheory.yoneda.obj Y).map ((Qₛ).map f).op).op)
    infer_instance
  have h' := (MorphismProperty.IsInvertedBy.map_iff Wᵢ Qₛ
    (CategoryTheory.yoneda.obj Y).rightOp).2 h
  simpa only [Functor.rightOp_leftOp_eq] using h'.leftOp

/-- Interval localization is bijective on maps into an actual interval-local target. -/
theorem stalkwiseToIntervalHomotopyCategory_map_bijective
    (Y : StalkwiseHomotopyCategory.{w} C J) (hY : IsIntervalLocal C J I Y)
    (X : StalkwiseHomotopyCategory.{w} C J) :
    Function.Bijective (fun f : X ⟶ Y ↦ (L).map f) := by
  let V := (Wᵢ).map Qₛ
  let F := Localization.lift (W := V.op) (CategoryTheory.yoneda.obj Y)
    (isInvertedBy_intervalImage_yoneda C J I Y hY) (L).op
  let α : (L).op ⋙ F ≅ CategoryTheory.yoneda.obj Y :=
    Localization.fac (W := V.op) (CategoryTheory.yoneda.obj Y)
      (isInvertedBy_intervalImage_yoneda C J I Y hY) (L).op
  let e (Z : StalkwiseHomotopyCategory.{w} C J) :
      (Z ⟶ Y) ≃ F.obj (op ((L).obj Z)) := (α.app (op Z)).symm.toEquiv
  have hNat {Z Z' : StalkwiseHomotopyCategory.{w} C J}
      (f : Z ⟶ Z') (g : Z' ⟶ Y) :
      e Z (f ≫ g) = F.map ((L).map f).op (e Z' g) :=
    ConcreteCategory.congr_hom (α.inv.naturality f.op) g
  have hEq (Z : StalkwiseHomotopyCategory.{w} C J) {f g : Z ⟶ Y}
      (h : e Z f = e Z g) : (L).map f = (L).map g :=
    congrArg (L).map ((e Z).injective h)
  let e' := Localization.homEquivOfStrictMaps L V F Y (fun Z ↦ e Z) hNat
    (fun Z ↦ (e Z).surjective) (fun Z ↦ hEq Z) X
  let E := e'.trans (e X).symm
  have hE (f : X ⟶ Y) : E ((L).map f) = f := by
    dsimp only [E, Equiv.trans_apply]
    rw [Localization.homEquivOfStrictMaps_map]
    exact (e X).symm_apply_apply f
  refine ⟨?_, ?_⟩
  · intro f g h
    simpa only [hE] using congrArg E h
  · intro f
    exact ⟨E f, E.injective (hE (E f))⟩

/-- Maps into a local stalkwise object are unchanged by the intermediate localization. -/
def stalkwiseIntervalLocalHomEquiv
    (Y : StalkwiseHomotopyCategory.{w} C J) (hY : IsIntervalLocal C J I Y)
    (X : StalkwiseHomotopyCategory.{w} C J) :
    ((L).obj X ⟶ (L).obj Y) ≃ (X ⟶ Y) :=
  (Equiv.ofBijective (fun f : X ⟶ Y ↦ (L).map f)
    (stalkwiseToIntervalHomotopyCategory_map_bijective C J I Y hY X)).symm

@[simp]
theorem stalkwiseIntervalLocalHomEquiv_map
    (Y : StalkwiseHomotopyCategory.{w} C J) (hY : IsIntervalLocal C J I Y)
    (X : StalkwiseHomotopyCategory.{w} C J) (f : X ⟶ Y) :
    stalkwiseIntervalLocalHomEquiv C J I Y hY X ((L).map f) = f :=
  (stalkwiseIntervalLocalHomEquiv C J I Y hY X).apply_symm_apply f

@[simp]
theorem stalkwiseIntervalLocalHomEquiv_symm_apply
    (Y : StalkwiseHomotopyCategory.{w} C J) (hY : IsIntervalLocal C J I Y)
    (X : StalkwiseHomotopyCategory.{w} C J) (f : X ⟶ Y) :
    (stalkwiseIntervalLocalHomEquiv C J I Y hY X).symm f = (L).map f := rfl

@[simp]
theorem map_stalkwiseIntervalLocalHomEquiv
    (Y : StalkwiseHomotopyCategory.{w} C J) (hY : IsIntervalLocal C J I Y)
    (X : StalkwiseHomotopyCategory.{w} C J) (f : (L).obj X ⟶ (L).obj Y) :
    (L).map (stalkwiseIntervalLocalHomEquiv C J I Y hY X f) = f :=
  (stalkwiseIntervalLocalHomEquiv C J I Y hY X).symm_apply_apply f

/-- The comparison respects precomposition by the actual stalkwise morphism. -/
theorem stalkwiseIntervalLocalHomEquiv_naturality
    (Y : StalkwiseHomotopyCategory.{w} C J) (hY : IsIntervalLocal C J I Y)
    {X X' : StalkwiseHomotopyCategory.{w} C J} (f : X ⟶ X')
    (g : (L).obj X' ⟶ (L).obj Y) :
    stalkwiseIntervalLocalHomEquiv C J I Y hY X ((L).map f ≫ g) =
      f ≫ stalkwiseIntervalLocalHomEquiv C J I Y hY X' g := by
  apply (stalkwiseToIntervalHomotopyCategory_map_bijective C J I Y hY X).1
  change (L).map (stalkwiseIntervalLocalHomEquiv C J I Y hY X ((L).map f ≫ g)) =
    (L).map (f ≫ stalkwiseIntervalLocalHomEquiv C J I Y hY X' g)
  rw [map_stalkwiseIntervalLocalHomEquiv, Functor.map_comp,
    map_stalkwiseIntervalLocalHomEquiv]

/-- Morphisms into a presheaf whose actual stalkwise image is interval-local
are the same in the two selected localizations. -/
def intervalLocalHomEquiv (Y : PointedSimplicialPresheaf.{w} C)
    (hY : IsIntervalLocal C J I ((Qₛ).obj Y)) (X : PointedSimplicialPresheaf.{w} C) :
    ((Qᵢ).obj X ⟶ (Qᵢ).obj Y) ≃ ((Qₛ).obj X ⟶ (Qₛ).obj Y) :=
  (Iso.homCongr ((stalkwiseToIntervalHomotopyCategoryCompIso C J I).app X).symm
      ((stalkwiseToIntervalHomotopyCategoryCompIso C J I).app Y).symm).trans
    (stalkwiseIntervalLocalHomEquiv C J I ((Qₛ).obj Y) hY ((Qₛ).obj X))

/-- The comparison retains the image of the original presheaf map. -/
@[simp]
theorem intervalLocalHomEquiv_map (Y : PointedSimplicialPresheaf.{w} C)
    (hY : IsIntervalLocal C J I ((Qₛ).obj Y)) (X : PointedSimplicialPresheaf.{w} C)
    (f : X ⟶ Y) :
    intervalLocalHomEquiv C J I Y hY X ((Qᵢ).map f) = (Qₛ).map f := by
  let α := stalkwiseToIntervalHomotopyCategoryCompIso C J I
  change stalkwiseIntervalLocalHomEquiv C J I ((Qₛ).obj Y) hY ((Qₛ).obj X)
    (α.hom.app X ≫ (Qᵢ).map f ≫ α.inv.app Y) = (Qₛ).map f
  rw [← α.hom.naturality_assoc f, α.hom_inv_id_app Y, Category.comp_id]
  exact stalkwiseIntervalLocalHomEquiv_map C J I ((Qₛ).obj Y) hY ((Qₛ).obj X) ((Qₛ).map f)

/-- The comparison respects precomposition by the original presheaf map. -/
theorem intervalLocalHomEquiv_naturality (Y : PointedSimplicialPresheaf.{w} C)
    (hY : IsIntervalLocal C J I ((Qₛ).obj Y))
    {X X' : PointedSimplicialPresheaf.{w} C} (f : X ⟶ X')
    (g : (Qᵢ).obj X' ⟶ (Qᵢ).obj Y) :
    intervalLocalHomEquiv C J I Y hY X ((Qᵢ).map f ≫ g) =
      (Qₛ).map f ≫ intervalLocalHomEquiv C J I Y hY X' g := by
  let α := stalkwiseToIntervalHomotopyCategoryCompIso C J I
  change stalkwiseIntervalLocalHomEquiv C J I ((Qₛ).obj Y) hY ((Qₛ).obj X)
      (α.hom.app X ≫ ((Qᵢ).map f ≫ g) ≫ α.inv.app Y) =
    (Qₛ).map f ≫ stalkwiseIntervalLocalHomEquiv C J I ((Qₛ).obj Y) hY ((Qₛ).obj X')
      (α.hom.app X' ≫ g ≫ α.inv.app Y)
  simp only [Category.assoc]
  rw [← α.hom.naturality_assoc f]
  exact stalkwiseIntervalLocalHomEquiv_naturality C J I ((Qₛ).obj Y) hY ((Qₛ).map f) _

end CategoryTheory.PointedSimplicialPresheaf
