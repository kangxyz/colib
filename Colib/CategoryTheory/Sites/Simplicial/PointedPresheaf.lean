/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.Realization.MorphismProperty
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Yoneda

/-!
# Pointed simplicial presheaves

The selected category is the native under category of the terminal simplicial
presheaf. Free pointing is the categorical disjoint union with the terminal
presheaf. Discrete Yoneda and its pointed version retain the original maps.

The weak equivalences in this file are objectwise realization weak equivalences.
No Nisnevich descent or affine-line localization is asserted at this layer.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe w v u

namespace CategoryTheory

/-- Pointed simplicial presheaves, using the native under category of the
terminal simplicial presheaf. -/
abbrev PointedSimplicialPresheaf (C : Type u) [Category.{v} C] :=
  Under (⊤_ (Cᵒᵖ ⥤ SSet.{w}))

namespace PointedSimplicialPresheaf

variable (C : Type u) [Category.{v} C]

/-- Forget the global basepoint. -/
abbrev forget : PointedSimplicialPresheaf.{w} C ⥤ Cᵒᵖ ⥤ SSet.{w} :=
  Under.forget _

/-- Evaluation retains the underlying simplicial set at the specified object. -/
def evaluation (U : Cᵒᵖ) : PointedSimplicialPresheaf.{w} C ⥤ SSet.{w} :=
  forget C ⋙ (CategoryTheory.evaluation Cᵒᵖ SSet).obj U

/-- The one-point pointed presheaf. -/
def point : PointedSimplicialPresheaf.{w} C :=
  Under.mk (𝟙 (⊤_ (Cᵒᵖ ⥤ SSet.{w})))

/-- The unique pointed map from the one-point presheaf. -/
def fromPoint (F : PointedSimplicialPresheaf.{w} C) : point C ⟶ F :=
  Under.homMk F.hom (by simp [point])

/-- The unique pointed map to the one-point presheaf. -/
def toPoint (F : PointedSimplicialPresheaf.{w} C) : F ⟶ point C :=
  Under.homMk (terminal.from F.right) (terminal.hom_ext _ _)

/-- The one-point presheaf is both initial and terminal in the pointed category. -/
theorem point_isZero : IsZero (point.{w} C) where
  unique_to F := ⟨{
    default := fromPoint C F
    uniq f := by
      apply Under.UnderMorphism.ext
      change f.right = F.hom
      simpa only [point, Under.mk_hom, Category.id_comp] using Under.w f }⟩
  unique_from F := ⟨{
    default := toPoint C F
    uniq f := by
      apply Under.UnderMorphism.ext
      exact terminal.hom_ext _ _ }⟩

instance : HasZeroObject (PointedSimplicialPresheaf.{w} C) :=
  (point_isZero C).hasZeroObject

/-- The constant pointed map has the target's actual global basepoint. -/
def constant (F G : PointedSimplicialPresheaf.{w} C) : F ⟶ G :=
  Under.homMk (terminal.from F.right ≫ G.hom) (by
    rw [← Category.assoc, terminal.hom_ext (F.hom ≫ terminal.from F.right) (𝟙 _),
      Category.id_comp])

instance : HasZeroMorphisms (PointedSimplicialPresheaf.{w} C) where
  zero F G := ⟨constant C F G⟩
  comp_zero {F G} f H := by
    apply Under.UnderMorphism.ext
    change f.right ≫ (terminal.from G.right ≫ H.hom) = terminal.from F.right ≫ H.hom
    rw [← Category.assoc, terminal.comp_from]
  zero_comp F {G H} f := by
    apply Under.UnderMorphism.ext
    change (terminal.from F.right ≫ G.hom) ≫ f.right = terminal.from F.right ≫ H.hom
    rw [Category.assoc, Under.w]

@[simp]
theorem zero_right (F G : PointedSimplicialPresheaf.{w} C) :
    (0 : F ⟶ G).right = terminal.from F.right ≫ G.hom := rfl

/-- Freely adjoin a disjoint basepoint to a simplicial presheaf. -/
def free : (Cᵒᵖ ⥤ SSet.{w}) ⥤ PointedSimplicialPresheaf.{w} C where
  obj F := Under.mk (coprod.inr : (⊤_ (Cᵒᵖ ⥤ SSet.{w})) ⟶ F ⨿ ⊤_ _)
  map f := Under.homMk (coprod.map f (𝟙 _)) (by simp)
  map_id F := by
    apply Under.UnderMorphism.ext
    exact coprod.map_id_id
  map_comp f g := by
    apply Under.UnderMorphism.ext
    simp only [Under.homMk_right, Under.comp_right, coprod.map_map, Category.id_comp]

@[simp]
theorem free_obj_right (F : Cᵒᵖ ⥤ SSet.{w}) :
    ((free C).obj F).right = (F ⨿ ⊤_ (Cᵒᵖ ⥤ SSet.{w})) := rfl

@[simp]
theorem free_obj_hom (F : Cᵒᵖ ⥤ SSet.{w}) :
    ((free C).obj F).hom = coprod.inr := rfl

@[simp]
theorem free_map_right {F G : Cᵒᵖ ⥤ SSet.{w}} (f : F ⟶ G) :
    ((free C).map f).right = coprod.map f (𝟙 _) := rfl

/-- The inclusion of the original presheaf into its free pointed presheaf. -/
def freeInclusion (F : Cᵒᵖ ⥤ SSet.{w}) : F ⟶ ((free C).obj F).right :=
  coprod.inl

@[reassoc]
theorem freeInclusion_naturality {F G : Cᵒᵖ ⥤ SSet.{w}} (f : F ⟶ G) :
    freeInclusion C F ≫ ((free C).map f).right = f ≫ freeInclusion C G := by
  exact coprod.inl_map _ _

/-- Maps from a freely pointed presheaf are precisely maps from the original
presheaf to the underlying target. -/
def freeHomEquiv (F : Cᵒᵖ ⥤ SSet.{w}) (G : PointedSimplicialPresheaf.{w} C) :
    ((free C).obj F ⟶ G) ≃ (F ⟶ G.right) where
  toFun f := coprod.inl ≫ f.right
  invFun f := Under.homMk (coprod.desc f G.hom) (coprod.inr_desc _ _)
  left_inv f := by
    apply Under.UnderMorphism.ext
    change coprod.desc (coprod.inl ≫ f.right) G.hom = f.right
    apply coprod.hom_ext
    · exact coprod.inl_desc _ _
    · rw [coprod.inr_desc]
      exact (Under.w f).symm
  right_inv f := by
    change coprod.inl ≫ coprod.desc f G.hom = f
    exact coprod.inl_desc _ _

@[simp]
theorem freeHomEquiv_apply (F : Cᵒᵖ ⥤ SSet.{w})
    (G : PointedSimplicialPresheaf.{w} C) (f : (free C).obj F ⟶ G) :
    freeHomEquiv C F G f = freeInclusion C F ≫ f.right := rfl

@[simp]
theorem freeHomEquiv_symm_right (F : Cᵒᵖ ⥤ SSet.{w})
    (G : PointedSimplicialPresheaf.{w} C) (f : F ⟶ G.right) :
    ((freeHomEquiv C F G).symm f).right = coprod.desc f G.hom := rfl

/-- Free pointing is left adjoint to forgetting the basepoint. -/
def freeForgetAdjunction : free.{w} C ⊣ forget C :=
  Adjunction.mkOfHomEquiv {
    homEquiv := freeHomEquiv C
    homEquiv_naturality_left_symm := by
      intro F F' G f g
      apply Under.UnderMorphism.ext
      change coprod.desc (f ≫ g) G.hom = coprod.map f (𝟙 _) ≫ coprod.desc g G.hom
      rw [coprod.map_desc, Category.id_comp]
    homEquiv_naturality_right := by
      intro F G H f g
      change coprod.inl ≫ (f.right ≫ g.right) = (coprod.inl ≫ f.right) ≫ g.right
      exact (Category.assoc _ _ _).symm }

/-- Yoneda regarded as a presheaf of discrete simplicial sets. -/
def simplicialYoneda : C ⥤ Cᵒᵖ ⥤ SSet.{v} :=
  CategoryTheory.yoneda ⋙
    (Functor.whiskeringRight _ _ _).obj (Functor.const SimplexCategoryᵒᵖ)

@[simp]
theorem simplicialYoneda_obj_obj_obj (U : C) (T : Cᵒᵖ) (n : SimplexCategoryᵒᵖ) :
    (((simplicialYoneda C).obj U).obj T).obj n = (T.unop ⟶ U) := rfl

/-- The discrete Yoneda map is the original postcomposition map in every degree. -/
theorem simplicialYoneda_map_app_app {U V : C} (f : U ⟶ V)
    (T : Cᵒᵖ) (n : SimplexCategoryᵒᵖ) (g : T.unop ⟶ U) :
    (((simplicialYoneda C).map f).app T).app n g = g ≫ f := rfl

/-- The actual pointed representable, with its freely adjoined basepoint. -/
def yoneda : C ⥤ PointedSimplicialPresheaf.{v} C :=
  simplicialYoneda C ⋙ free C

@[simp]
theorem yoneda_obj_right (U : C) :
    ((yoneda C).obj U).right = ((simplicialYoneda C).obj U ⨿ ⊤_ _) := rfl

@[simp]
theorem yoneda_obj_hom (U : C) : ((yoneda C).obj U).hom = coprod.inr := rfl

@[simp]
theorem yoneda_map_right {U V : C} (f : U ⟶ V) :
    ((yoneda C).map f).right = coprod.map ((simplicialYoneda C).map f) (𝟙 _) := rfl

/-- Objectwise weak equivalences of the actual pointed simplicial presheaves. -/
def objectwiseWeakEquivalences : MorphismProperty (PointedSimplicialPresheaf.{w} C) :=
  fun _ _ f ↦ ∀ U, SSet.realizationWeakEquivalences (f.right.app U)

@[simp]
theorem objectwiseWeakEquivalences_iff {F G : PointedSimplicialPresheaf.{w} C}
    (f : F ⟶ G) : objectwiseWeakEquivalences C f ↔
      ∀ U, SSet.IsRealizationWeakEquivalence (f.right.app U) := Iff.rfl

instance : (objectwiseWeakEquivalences.{w} C).IsMultiplicative where
  id_mem F U := SSet.realizationWeakEquivalences.id_mem (F.right.obj U)
  comp_mem f g hf hg U := SSet.realizationWeakEquivalences.comp_mem
    (f.right.app U) (g.right.app U) (hf U) (hg U)

instance : (objectwiseWeakEquivalences.{w} C).HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg U := SSet.realizationWeakEquivalences.of_postcomp
    (f.right.app U) (g.right.app U) (hg U) (hfg U)
  of_precomp f g hf hfg U := SSet.realizationWeakEquivalences.of_precomp
    (f.right.app U) (g.right.app U) (hf U) (hfg U)

/-- A pointed isomorphism is an objectwise weak equivalence. -/
theorem objectwiseWeakEquivalences_of_isIso {F G : PointedSimplicialPresheaf.{w} C}
    (f : F ⟶ G) [IsIso f] : objectwiseWeakEquivalences C f :=
  fun U ↦ SSet.realizationWeakEquivalences_of_isIso ((evaluation C U).map f)

instance : (objectwiseWeakEquivalences.{w} C).RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ f hf ↦ by
      let : IsIso f := hf
      exact objectwiseWeakEquivalences_of_isIso C f)

end PointedSimplicialPresheaf

end CategoryTheory

attribute [colib_tag "COL-0385"]
  CategoryTheory.PointedSimplicialPresheaf.freeForgetAdjunction
  CategoryTheory.PointedSimplicialPresheaf.yoneda
  CategoryTheory.PointedSimplicialPresheaf.objectwiseWeakEquivalences
