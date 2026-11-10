/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.CategoryTheory.Sites.Simplicial.StalkwiseWeakEquivalence
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Sheafification and the actual fibers of pointed simplicial presheaves

The native class `J.W` is inverted by every actual site fiber. Consequently,
a pointed map whose underlying map lies in `J.W` is a stalkwise realization
weak equivalence in the selected pointed presheaf model.

With actual left exact sheafification, its terminal comparison transports
the global basepoint and gives an endofunctor of the same native under
category. The pointed sheafification unit is an isomorphism on every fiber.
No enough-points theorem or affine-line homotopical comparison is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable (C : Type u) [Category.{v} C] (J : GrothendieckTopology C)

/-- A site fiber inverts the native sheafification class of the underlying map. -/
theorem isIso_fiberAtPoint_map_of_W (Φ : J.Point.{w})
    {F G : PointedSimplicialPresheaf.{w} C} (f : F ⟶ G) (hf : J.W f.right) :
    IsIso ((fiberAtPoint C Φ).map f) := by
  change IsIso (Φ.presheafFiber.map f.right)
  exact Φ.W_isInvertedBy_presheafFiber f.right hf

/-- The native sheafification class on underlying maps is contained in the
selected stalkwise realization weak-equivalence class. -/
theorem stalkwiseWeakEquivalences_of_W
    {F G : PointedSimplicialPresheaf.{w} C} (f : F ⟶ G) (hf : J.W f.right) :
    stalkwiseWeakEquivalences C J f := by
  intro Φ
  let : IsIso ((fiberAtPoint C Φ).map f) := isIso_fiberAtPoint_map_of_W C J Φ f hf
  exact SSet.realizationWeakEquivalences_of_isIso _

/-- The inclusion of morphism properties retains the exact forgetful functor. -/
theorem inverseImage_W_le_stalkwiseWeakEquivalences :
    J.W.inverseImage (forget.{w} C) ≤ stalkwiseWeakEquivalences C J :=
  fun _ _ f hf ↦ stalkwiseWeakEquivalences_of_W C J f hf

section WeakSheafification

variable [HasWeakSheafify J SSet.{w}]

/-- An isomorphism after actual simplicial sheafification is an isomorphism
on every actual site fiber. -/
theorem isIso_fiberAtPoint_map_of_isIso_sheafification (Φ : J.Point.{w})
    {F G : PointedSimplicialPresheaf.{w} C} (f : F ⟶ G)
    [IsIso ((presheafToSheaf J SSet.{w}).map f.right)] :
    IsIso ((fiberAtPoint C Φ).map f) :=
  isIso_fiberAtPoint_map_of_W C J Φ f ((J.W_iff f.right).2 inferInstance)

/-- Actual sheafification-isomorphisms give stalkwise weak equivalences. -/
theorem stalkwiseWeakEquivalences_of_isIso_sheafification
    {F G : PointedSimplicialPresheaf.{w} C} (f : F ⟶ G)
    [IsIso ((presheafToSheaf J SSet.{w}).map f.right)] :
    stalkwiseWeakEquivalences C J f :=
  stalkwiseWeakEquivalences_of_W C J f ((J.W_iff f.right).2 inferInstance)

end WeakSheafification

section Sheafification

variable [HasSheafify J SSet.{w}]

/-- The native terminal comparison for actual simplicial sheafification. -/
def sheafificationTerminalIso :
    CategoryTheory.sheafify J (⊤_ (Cᵒᵖ ⥤ SSet.{w})) ≅ ⊤_ (Cᵒᵖ ⥤ SSet.{w}) :=
  PreservesTerminal.iso (CategoryTheory.sheafification J SSet.{w})

/-- On the terminal presheaf, the actual unit is the inverse terminal comparison. -/
theorem toSheafify_terminal_eq_inv :
    CategoryTheory.toSheafify J (⊤_ (Cᵒᵖ ⥤ SSet.{w})) =
      (sheafificationTerminalIso C J).inv :=
  (isLimitOfHasTerminalOfPreservesLimit
    (CategoryTheory.sheafification J SSet.{w})).hom_ext _ _

/-- Sheafification in the selected under category, with the global basepoint
transported by the native terminal isomorphism. -/
def sheafificationFunctor : PointedSimplicialPresheaf.{w} C ⥤
    PointedSimplicialPresheaf.{w} C :=
  Under.post (X := ⊤_ (Cᵒᵖ ⥤ SSet.{w}))
      (CategoryTheory.sheafification J SSet.{w}) ⋙
    Under.map (sheafificationTerminalIso C J).inv

@[simp]
theorem sheafificationFunctor_obj_right (F : PointedSimplicialPresheaf.{w} C) :
    ((sheafificationFunctor C J).obj F).right = CategoryTheory.sheafify J F.right := rfl

/-- The new global point is the image of the original one after terminal transport. -/
@[simp]
theorem sheafificationFunctor_obj_hom (F : PointedSimplicialPresheaf.{w} C) :
    ((sheafificationFunctor C J).obj F).hom =
      (sheafificationTerminalIso C J).inv ≫ CategoryTheory.sheafifyMap J F.hom := rfl

@[simp]
theorem sheafificationFunctor_map_right
    {F G : PointedSimplicialPresheaf.{w} C} (f : F ⟶ G) :
    ((sheafificationFunctor C J).map f).right = CategoryTheory.sheafifyMap J f.right := rfl

/-- The result is an actual sheaf of simplicial sets, in the same underlying model. -/
theorem isSheaf_sheafificationFunctor_obj_right (F : PointedSimplicialPresheaf.{w} C) :
    Presheaf.IsSheaf J ((sheafificationFunctor C J).obj F).right :=
  ((presheafToSheaf J SSet.{w}).obj F.right).property

/-- The original sheafification unit preserves the transported global basepoint. -/
def toSheafification (F : PointedSimplicialPresheaf.{w} C) :
    F ⟶ (sheafificationFunctor C J).obj F :=
  Under.homMk (CategoryTheory.toSheafify J F.right) (by
    change F.hom ≫ CategoryTheory.toSheafify J F.right =
      (sheafificationTerminalIso C J).inv ≫ CategoryTheory.sheafifyMap J F.hom
    rw [CategoryTheory.toSheafify_naturality, toSheafify_terminal_eq_inv])

@[simp]
theorem toSheafification_right (F : PointedSimplicialPresheaf.{w} C) :
    (toSheafification C J F).right = CategoryTheory.toSheafify J F.right := rfl

/-- The pointed sheafification units form a natural transformation. -/
def sheafificationUnit : 𝟭 (PointedSimplicialPresheaf.{w} C) ⟶ sheafificationFunctor C J where
  app := toSheafification C J
  naturality F G f := by
    apply Under.UnderMorphism.ext
    change f.right ≫ CategoryTheory.toSheafify J G.right =
      CategoryTheory.toSheafify J F.right ≫ CategoryTheory.sheafifyMap J f.right
    exact CategoryTheory.toSheafify_naturality J f.right

/-- The pointed unit induces an actual simplicial-set isomorphism at every site point. -/
theorem isIso_fiberAtPoint_toSheafification (Φ : J.Point.{w})
    (F : PointedSimplicialPresheaf.{w} C) :
    IsIso ((fiberAtPoint C Φ).map (toSheafification C J F)) :=
  isIso_fiberAtPoint_map_of_W C J Φ (toSheafification C J F) (J.W_toSheafify F.right)

/-- The actual pointed sheafification unit is a stalkwise weak equivalence. -/
theorem stalkwiseWeakEquivalences_toSheafification (F : PointedSimplicialPresheaf.{w} C) :
    stalkwiseWeakEquivalences C J (toSheafification C J F) :=
  stalkwiseWeakEquivalences_of_W C J (toSheafification C J F) (J.W_toSheafify F.right)

/-- Pointed sheafification preserves and reflects the selected stalkwise weak equivalences. -/
theorem stalkwiseWeakEquivalences_sheafificationFunctor_map_iff
    {F G : PointedSimplicialPresheaf.{w} C} (f : F ⟶ G) :
    stalkwiseWeakEquivalences C J ((sheafificationFunctor C J).map f) ↔
      stalkwiseWeakEquivalences C J f := by
  have hF := stalkwiseWeakEquivalences_toSheafification C J F
  have hG := stalkwiseWeakEquivalences_toSheafification C J G
  have h := (sheafificationUnit C J).naturality f
  change f ≫ toSheafification C J G =
    toSheafification C J F ≫ (sheafificationFunctor C J).map f at h
  constructor
  · intro hf
    apply (stalkwiseWeakEquivalences C J).of_postcomp _ _ hG
    rw [h]
    exact (stalkwiseWeakEquivalences C J).comp_mem _ _ hF hf
  · intro hf
    apply (stalkwiseWeakEquivalences C J).of_precomp _ _ hF
    rw [← h]
    exact (stalkwiseWeakEquivalences C J).comp_mem _ _ hf hG

/-- The pointed unit is invertible in the formal localization at the selected stalkwise class. -/
theorem isIso_localized_toSheafification (F : PointedSimplicialPresheaf.{w} C) :
    IsIso ((toStalkwiseHomotopyCategory C J).map (toSheafification C J F)) :=
  isIso_toStalkwiseHomotopyCategory_map C (toSheafification C J F)
    (stalkwiseWeakEquivalences_toSheafification C J F)

end Sheafification

end CategoryTheory.PointedSimplicialPresheaf

attribute [colib_tag "COL-0390"]
  CategoryTheory.PointedSimplicialPresheaf.stalkwiseWeakEquivalences_of_W
  CategoryTheory.PointedSimplicialPresheaf.sheafificationUnit
  CategoryTheory.PointedSimplicialPresheaf.stalkwiseWeakEquivalences_sheafificationFunctor_map_iff
  CategoryTheory.PointedSimplicialPresheaf.isIso_localized_toSheafification
