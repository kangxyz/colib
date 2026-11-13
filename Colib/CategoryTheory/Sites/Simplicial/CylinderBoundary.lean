/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.SimplicialCylinder
public import Colib.CategoryTheory.Sites.Simplicial.StalkwiseTrivialCoproduct

/-!
# The endpoint pair and boundary map of the pointed simplicial cylinder

The original endpoint maps define the boundary pushout. The map from
that pushout keeps the actual parameterized cylinder and its basepoint.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable {C : Type u} [Category.{v} C]

/-- The original pointed map of cylinders induced by a map of pointed objects. -/
def parameterizedCylinderMap {A B : PointedSimplicialPresheaf.{w} C} (f : A ⟶ B)
    (K : Cᵒᵖ ⥤ SSet.{w}) : parameterizedCylinder A K ⟶ parameterizedCylinder B K :=
  Under.homMk (pushout.map (intervalAxis A K) (terminal.from K) (intervalAxis B K)
    (terminal.from K) (prod.map f.right (𝟙 K)) (𝟙 _) (𝟙 K)
    (by apply prod.hom_ext <;> simp [intervalAxis, Under.w])
    (by rw [Category.id_comp, Category.comp_id]))
    (by simp)

@[reassoc]
theorem parameterizedCylinderMap_projection {A B : PointedSimplicialPresheaf.{w} C} (f : A ⟶ B)
    (K : Cᵒᵖ ⥤ SSet.{w}) :
    parameterizedCylinderMap f K ≫ cylinderProjection B K = cylinderProjection A K ≫ f := by
  apply Under.UnderMorphism.ext
  apply pushout.hom_ext
  · simp only [parameterizedCylinderMap, cylinderProjection, Under.comp_right, Under.homMk_right,
      Category.assoc, pushout.map, pushout.inl_desc_assoc, pushout.inl_desc, prod.map_fst]
  · simp only [parameterizedCylinderMap, cylinderProjection, Under.comp_right, Under.homMk_right,
      pushout.map, Category.id_comp, pushout.inr_desc_assoc,
      pushout.inr_desc, Under.w]

@[reassoc]
theorem cylinderSection_parameterizedCylinderMap {A B : PointedSimplicialPresheaf.{w} C}
    (f : A ⟶ B) {K : Cᵒᵖ ⥤ SSet.{w}} (s : (⊤_ (Cᵒᵖ ⥤ SSet.{w})) ⟶ K) :
    cylinderSection A s ≫ parameterizedCylinderMap f K = f ≫ cylinderSection B s := by
  have h : prod.lift (𝟙 A.right) (terminal.from A.right ≫ s) ≫ prod.map f.right (𝟙 K) =
      f.right ≫ prod.lift (𝟙 B.right) (terminal.from B.right ≫ s) := by
    apply prod.hom_ext <;> simp
  apply Under.UnderMorphism.ext
  simp only [cylinderSection, parameterizedCylinderMap, Under.comp_right, Under.homMk_right,
    Category.assoc, pushout.map, pushout.inl_desc]
  exact (reassoc_of% h) _

/-- The actual map from both pointed endpoint copies into the cylinder. -/
def simplicialEndpointPair (A : PointedSimplicialPresheaf.{w} C) :
    A ⨿ A ⟶ parameterizedCylinder A (interval C) :=
  coprod.desc (cylinderSection A (intervalEndpoint C 0)) (cylinderSection A (intervalEndpoint C 1))

@[reassoc]
theorem simplicialEndpointPair_naturality {A B : PointedSimplicialPresheaf.{w} C} (f : A ⟶ B) :
    simplicialEndpointPair A ≫ parameterizedCylinderMap f (interval C) =
      coprod.map f f ≫ simplicialEndpointPair B := by
  apply coprod.hom_ext
  · simp only [simplicialEndpointPair, coprod.inl_desc_assoc, coprod.inl_map_assoc, coprod.inl_desc,
      cylinderSection_parameterizedCylinderMap]
  · simp only [simplicialEndpointPair, coprod.inr_desc_assoc, coprod.inr_map_assoc, coprod.inr_desc,
      cylinderSection_parameterizedCylinderMap]

/-- The relative cylinder boundary, retaining both endpoint maps on the target. -/
abbrev cylinderBoundary {A B : PointedSimplicialPresheaf.{w} C} (f : A ⟶ B) :=
  pushout (simplicialEndpointPair A) (coprod.map f f)

/-- The actual boundary inclusion into the target cylinder. -/
def cylinderBoundaryMap {A B : PointedSimplicialPresheaf.{w} C} (f : A ⟶ B) :
    cylinderBoundary f ⟶ parameterizedCylinder B (interval C) :=
  pushout.desc (parameterizedCylinderMap f (interval C)) (simplicialEndpointPair B)
    (simplicialEndpointPair_naturality f)

@[reassoc]
theorem cylinderBoundary_inl_map {A B : PointedSimplicialPresheaf.{w} C} (f : A ⟶ B) :
    pushout.inl (simplicialEndpointPair A) (coprod.map f f) ≫ cylinderBoundaryMap f =
      parameterizedCylinderMap f (interval C) := pushout.inl_desc _ _ _

@[reassoc]
theorem cylinderBoundary_inr_map {A B : PointedSimplicialPresheaf.{w} C} (f : A ⟶ B) :
    pushout.inr (simplicialEndpointPair A) (coprod.map f f) ≫ cylinderBoundaryMap f =
      simplicialEndpointPair B := pushout.inr_desc _ _ _

variable [LocallySmall.{w} C] (J : GrothendieckTopology C)

/-- A weak map induces a weak map between the original pointed cylinders. -/
theorem stalkwiseWeakEquivalences_parameterizedCylinderMap
    {A B : PointedSimplicialPresheaf.{w} C} {f : A ⟶ B}
    (hf : stalkwiseWeakEquivalences C J f) :
    stalkwiseWeakEquivalences C J (parameterizedCylinderMap f (interval C)) := by
  let W := stalkwiseWeakEquivalences.{w} C J
  apply W.of_postcomp _ _ (stalkwiseWeakEquivalences_cylinderProjection_interval C J B)
  rw [parameterizedCylinderMap_projection]
  exact W.comp_mem _ _ (stalkwiseWeakEquivalences_cylinderProjection_interval C J A) hf

/-- If the original map is stalkwise trivial, the boundary inclusion is weak. -/
theorem stalkwiseWeakEquivalences_cylinderBoundaryMap
    {A B : PointedSimplicialPresheaf.{w} C} {f : A ⟶ B}
    (hf : stalkwiseTrivialMonomorphisms C J f) :
    stalkwiseWeakEquivalences C J (cylinderBoundaryMap f) := by
  have hcoprod : stalkwiseTrivialMonomorphisms C J (coprod.map f f) := by
    let W := stalkwiseTrivialMonomorphisms.{w} C J
    change W (colimMap (mapPair (F := pair A A) (G := pair B B) f f))
    exact MorphismProperty.coproducts_le.{w} W _
      (MorphismProperty.coproducts_of_small.{w} W _ (MorphismProperty.colimitsOfShape_colimMap
        (mapPair (F := pair A A) (G := pair B B) f f) (fun j => by
          rcases j with ⟨_ | _⟩ <;> exact hf)))
  let W := stalkwiseTrivialMonomorphisms.{w} C J
  have h := W.of_isPushout (IsPushout.of_hasPushout (simplicialEndpointPair A) (coprod.map f f))
    hcoprod
  apply (stalkwiseWeakEquivalences.{w} C J).of_precomp _ _ h.2
  rw [cylinderBoundary_inl_map]
  exact stalkwiseWeakEquivalences_parameterizedCylinderMap J hf.2

end CategoryTheory.PointedSimplicialPresheaf
