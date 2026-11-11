/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.CategoryTheory.Sites.Simplicial.StalkwiseWeakEquivalence
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Interval localization of the stalkwise homotopy category

The pointed cylinder collapses the basepoint times the interval in the
ordinary product. Locality tests the projections of these cylinders in
the already stalkwise-localized category. A map is an interval
equivalence if precomposition into every such local object is a
bijection. This is the pointed presheaf analogue of the interval tests in
Morel–Voevodsky, §2.3, Definition 3.1 and Remark 3.3.

The site-specific comparison and a local replacement theorem are
additional obligations.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable {C : Type u} [Category.{v} C]

/-- The interval over the basepoint of a pointed simplicial presheaf. -/
def intervalAxis (X : PointedSimplicialPresheaf.{w} C) (I : Cᵒᵖ ⥤ SSet.{w}) :
    I ⟶ X.right ⨯ I :=
  prod.lift (terminal.from I ≫ X.hom) (𝟙 I)

/-- The cylinder of `X` with parameter `I`, pointed by collapsing the basepoint axis. -/
abbrev parameterizedCylinder (X : PointedSimplicialPresheaf.{w} C) (I : Cᵒᵖ ⥤ SSet.{w}) :
    PointedSimplicialPresheaf.{w} C :=
  Under.mk (pushout.inr (intervalAxis X I) (terminal.from I))

/-- The actual projection of the pointed cylinder. -/
def cylinderProjection (X : PointedSimplicialPresheaf.{w} C) (I : Cᵒᵖ ⥤ SSet.{w}) :
    parameterizedCylinder X I ⟶ X :=
  Under.homMk (pushout.desc prod.fst X.hom (by simp [intervalAxis]))
    (pushout.inr_desc _ _ _)

/-- The cylinder section associated to a global point of the parameter. -/
def cylinderSection (X : PointedSimplicialPresheaf.{w} C) {I : Cᵒᵖ ⥤ SSet.{w}}
    (i : (⊤_ (Cᵒᵖ ⥤ SSet.{w})) ⟶ I) : X ⟶ parameterizedCylinder X I :=
  Under.homMk (prod.lift (𝟙 X.right) (terminal.from X.right ≫ i) ≫
    pushout.inl (intervalAxis X I) (terminal.from I)) (by
      have hid : terminal.from (⊤_ (Cᵒᵖ ⥤ SSet.{w})) = 𝟙 _ := terminal.hom_ext _ _
      have h : X.hom ≫ prod.lift (𝟙 X.right) (terminal.from X.right ≫ i) =
          i ≫ intervalAxis X I := by
        apply prod.hom_ext <;> simp [intervalAxis, hid]
      rw [← Category.assoc, h, Category.assoc, pushout.condition]
      change i ≫ terminal.from I ≫ pushout.inr (intervalAxis X I) (terminal.from I) =
        pushout.inr (intervalAxis X I) (terminal.from I)
      rw [← Category.assoc, terminal.comp_from, hid, Category.id_comp])

@[reassoc (attr := simp)]
theorem cylinderSection_projection (X : PointedSimplicialPresheaf.{w} C)
    {I : Cᵒᵖ ⥤ SSet.{w}} (i : (⊤_ (Cᵒᵖ ⥤ SSet.{w})) ⟶ I) :
    cylinderSection X i ≫ cylinderProjection X I = 𝟙 X := by
  apply Under.UnderMorphism.ext
  change (prod.lift (𝟙 X.right) (terminal.from X.right ≫ i) ≫
      pushout.inl (intervalAxis X I) (terminal.from I)) ≫
    pushout.desc prod.fst X.hom _ = 𝟙 X.right
  rw [Category.assoc, pushout.inl_desc, prod.lift_fst]

variable (C : Type u) [Category.{v} C] (J : GrothendieckTopology C)

/-- A local object for the interval, tested on the actual pointed cylinder projections. -/
def IsIntervalLocal (I : Cᵒᵖ ⥤ SSet.{w}) (L : StalkwiseHomotopyCategory.{w} C J) : Prop :=
  ∀ X : PointedSimplicialPresheaf.{w} C, Function.Bijective
    (fun f : (toStalkwiseHomotopyCategory C J).obj X ⟶ L ↦
      (toStalkwiseHomotopyCategory C J).map (cylinderProjection X I) ≫ f)

/-- Maps inducing bijections into all interval-local objects after stalkwise localization. -/
def intervalWeakEquivalences (I : Cᵒᵖ ⥤ SSet.{w}) :
    MorphismProperty (PointedSimplicialPresheaf.{w} C) :=
  fun _ Y f ↦ ∀ (L : StalkwiseHomotopyCategory.{w} C J), IsIntervalLocal C J I L →
    Function.Bijective (fun g : (toStalkwiseHomotopyCategory C J).obj Y ⟶ L ↦
      (toStalkwiseHomotopyCategory C J).map f ≫ g)

/-- The original cylinder projection belongs to the interval-equivalence class. -/
theorem cylinderProjection_intervalWeakEquivalences (I : Cᵒᵖ ⥤ SSet.{w})
    (X : PointedSimplicialPresheaf.{w} C) :
    intervalWeakEquivalences C J I (cylinderProjection X I) :=
  fun _ hL ↦ hL X

/-- Stalkwise weak equivalences also pass every interval-local test. -/
theorem stalkwiseWeakEquivalences_le_intervalWeakEquivalences (I : Cᵒᵖ ⥤ SSet.{w}) :
    stalkwiseWeakEquivalences.{w} C J ≤ intervalWeakEquivalences C J I := by
  intro X Y f hf L _
  let e := @asIso _ _ _ _ ((toStalkwiseHomotopyCategory C J).map f)
    (isIso_toStalkwiseHomotopyCategory_map C f hf)
  refine ⟨?_, ?_⟩
  · intro g h eq
    calc
      g = e.inv ≫ (e.hom ≫ g) := by simp
      _ = e.inv ≫ (e.hom ≫ h) := congrArg (fun k ↦ e.inv ≫ k) eq
      _ = h := by simp
  · intro g
    exact ⟨e.inv ≫ g, by change e.hom ≫ e.inv ≫ g = g; simp⟩

/-- The formal localization at maps detected by the interval-local tests. -/
abbrev IntervalHomotopyCategory (I : Cᵒᵖ ⥤ SSet.{w}) :=
  (intervalWeakEquivalences C J I).Localization

/-- The original functor to the interval localization. -/
abbrev toIntervalHomotopyCategory (I : Cᵒᵖ ⥤ SSet.{w}) :
    PointedSimplicialPresheaf.{w} C ⥤ IntervalHomotopyCategory C J I :=
  (intervalWeakEquivalences C J I).Q

theorem isIso_toIntervalHomotopyCategory_map_cylinderProjection (I : Cᵒᵖ ⥤ SSet.{w})
    (X : PointedSimplicialPresheaf.{w} C) :
    IsIso ((toIntervalHomotopyCategory C J I).map (cylinderProjection X I)) :=
  (intervalWeakEquivalences C J I).Q_inverts _ (cylinderProjection_intervalWeakEquivalences C J I X)

/-- Sections at two actual global points give the same map in the interval localization. -/
theorem toIntervalHomotopyCategory_map_cylinderSection (I : Cᵒᵖ ⥤ SSet.{w})
    (X : PointedSimplicialPresheaf.{w} C) (i j : (⊤_ (Cᵒᵖ ⥤ SSet.{w})) ⟶ I) :
    (toIntervalHomotopyCategory C J I).map (cylinderSection X i) =
      (toIntervalHomotopyCategory C J I).map (cylinderSection X j) := by
  let Q := toIntervalHomotopyCategory C J I
  have hp : IsIso (Q.map (cylinderProjection X I)) :=
    isIso_toIntervalHomotopyCategory_map_cylinderProjection C J I X
  let e := @asIso _ _ _ _ (Q.map (cylinderProjection X I)) hp
  have h : Q.map (cylinderSection X i) ≫ e.hom = Q.map (cylinderSection X j) ≫ e.hom := by
    change Q.map (cylinderSection X i) ≫ Q.map (cylinderProjection X I) =
      Q.map (cylinderSection X j) ≫ Q.map (cylinderProjection X I)
    simp only [← Functor.map_comp, cylinderSection_projection]
  calc
    _ = (Q.map (cylinderSection X i) ≫ e.hom) ≫ e.inv := by
      rw [Category.assoc, e.hom_inv_id, Category.comp_id]
    _ = (Q.map (cylinderSection X j) ≫ e.hom) ≫ e.inv := congrArg (· ≫ e.inv) h
    _ = _ := by rw [Category.assoc, e.hom_inv_id, Category.comp_id]

/-- The endpoint maps of an actual pointed interval homotopy agree after localization. -/
theorem toIntervalHomotopyCategory_map_of_cylinder (I : Cᵒᵖ ⥤ SSet.{w})
    {X Y : PointedSimplicialPresheaf.{w} C} (h : parameterizedCylinder X I ⟶ Y)
    (i j : (⊤_ (Cᵒᵖ ⥤ SSet.{w})) ⟶ I) :
    (toIntervalHomotopyCategory C J I).map (cylinderSection X i ≫ h) =
      (toIntervalHomotopyCategory C J I).map (cylinderSection X j ≫ h) := by
  simp only [Functor.map_comp]
  rw [toIntervalHomotopyCategory_map_cylinderSection C J I X i j]

end CategoryTheory.PointedSimplicialPresheaf

attribute [colib_ref "MorelVoevodsky1999" "§2.3, Definition 3.1 and Remark 3.3, p. 86"
  "adaptation"
  "The pointed interval tests on the chosen stalkwise-localized presheaves"]
  CategoryTheory.PointedSimplicialPresheaf.IsIntervalLocal
