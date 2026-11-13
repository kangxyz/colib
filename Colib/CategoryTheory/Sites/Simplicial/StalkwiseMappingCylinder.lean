/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.CylinderEndpointMono
public import Colib.CategoryTheory.Sites.Simplicial.StalkwiseTrivialPushout
import Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms
import Mathlib.CategoryTheory.Limits.Over
import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory

/-!
# The mapping cylinder of a pointed simplicial presheaf

The mapping cylinder attaches one endpoint of the original pointed
cylinder along a given map. Its target inclusion is a stalkwise trivial
monomorphism, and its projection to the target is a stalkwise weak equivalence.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable {C : Type u} [Category.{v} C] {X Y : PointedSimplicialPresheaf.{w} C}

/-- The mapping cylinder uses the zero-indexed endpoint of the original
pointed simplicial cylinder as its attaching map. -/
abbrev mappingCylinder (f : X ⟶ Y) :=
  pushout (cylinderSection X (intervalEndpoint C 0)) f

/-- Include the target into the mapping cylinder. -/
abbrev mappingCylinderTarget (f : X ⟶ Y) : Y ⟶ mappingCylinder f :=
  pushout.inr (cylinderSection X (intervalEndpoint C 0)) f

/-- Include the source by the other endpoint of its cylinder. -/
def mappingCylinderSource (f : X ⟶ Y) : X ⟶ mappingCylinder f :=
  cylinderSection X (intervalEndpoint C 1) ≫
    pushout.inl (cylinderSection X (intervalEndpoint C 0)) f

/-- Collapse the cylinder to the target using the given map. -/
def mappingCylinderProjection (f : X ⟶ Y) : mappingCylinder f ⟶ Y :=
  pushout.desc (cylinderProjection X (interval C) ≫ f) (𝟙 Y) (by
    exact (cylinderSection_projection_assoc X (intervalEndpoint C 0) f).trans
      (Category.comp_id f).symm)

/-- The projection retracts the actual target inclusion. -/
@[reassoc]
theorem mappingCylinderTarget_projection (f : X ⟶ Y) :
    mappingCylinderTarget f ≫ mappingCylinderProjection f = 𝟙 Y :=
  pushout.inr_desc _ _ _

/-- The given map factors through the actual source inclusion. -/
@[reassoc]
theorem mappingCylinderSource_projection (f : X ⟶ Y) :
    mappingCylinderSource f ≫ mappingCylinderProjection f = f := by
  unfold mappingCylinderSource mappingCylinderProjection
  rw [Category.assoc, pushout.inl_desc]
  exact cylinderSection_projection_assoc X (intervalEndpoint C 1) f

/-- Both endpoints of the source cylinder are retained before the first
is attached to the target. The other endpoint inclusion is monic. -/
theorem mono_mappingCylinderSource (f : X ⟶ Y) : Mono (mappingCylinderSource f) := by
  let c₀ := cylinderSection X (intervalEndpoint C 0)
  let c₁ := cylinderSection X (intervalEndpoint C 1)
  let t := simplicialEndpointPair X
  let u : X ⟶ X ⨿ X := coprod.inl
  let v : Y ⟶ Y ⨿ X := coprod.inl
  let j := coprod.desc (mappingCylinderTarget f) (mappingCylinderSource f)
  let i := pushout.inl c₀ f
  have h₀ : u ≫ t = c₀ := coprod.inl_desc _ _
  have h₁ : v ≫ j = mappingCylinderTarget f := coprod.inl_desc _ _
  have hc : t ≫ i = coprod.map f (𝟙 X) ≫ j := by
    apply coprod.hom_ext
    · change u ≫ t ≫ i = u ≫ coprod.map f (𝟙 X) ≫ j
      rw [← Category.assoc u, h₀, coprod.inl_map_assoc, h₁]
      exact pushout.condition
    · simp only [t, j, simplicialEndpointPair, coprod.inr_desc_assoc, coprod.inr_map_assoc,
        Category.id_comp, coprod.inr_desc, mappingCylinderSource]
      rfl
  have hP : IsPushout (u ≫ t) f i (v ≫ j) := by
    rw [h₀, h₁]
    exact IsPushout.of_hasPushout c₀ f
  let e : IsPushout t (coprod.map f (𝟙 X)) i j :=
    hP.of_left hc (IsPushout.of_coprod_inl_with_id f X)
  let F := forget.{w} C
  let M := MorphismProperty.monomorphisms (Cᵒᵖ ⥤ SSet.{w})
  let : M.IsStableUnderCobaseChange := by
    change (MorphismProperty.monomorphisms (Cᵒᵖ ⥤ SSet.{w})).IsStableUnderCobaseChange
    rw [← MorphismProperty.functorCategory_monomorphisms]
    infer_instance
  let : Mono t := mono_simplicialEndpointPair X
  let : Mono (F.map t) := Under.mono_right_of_mono t
  let : Mono j.right := M.of_isPushout (e.map F).flip (inferInstanceAs (Mono (F.map t)))
  let : Mono j := Under.mono_of_mono_right j
  let j₁ : X ⟶ Y ⨿ X := coprod.inr
  let : Mono j₁ := inferInstanceAs (Mono (coprod.inr : X ⟶ Y ⨿ X))
  have hj : j₁ ≫ j = mappingCylinderSource f := coprod.inr_desc _ _
  rw [← hj]
  infer_instance

variable [LocallySmall.{w} C] (J : GrothendieckTopology C)

private theorem stalkwiseTrivialMonomorphisms_cylinderSection_interval
    (P : PointedSimplicialPresheaf.{w} C) (i : Fin 2) :
    stalkwiseTrivialMonomorphisms C J (cylinderSection P (intervalEndpoint C i)) := by
  let W := stalkwiseWeakEquivalences.{w} C J
  let p := cylinderProjection P (interval C)
  let s := cylinderSection P (intervalEndpoint C i)
  have h : s ≫ p = 𝟙 P := cylinderSection_projection P _
  exact ⟨mono_of_mono_fac h, W.of_postcomp s p
    (stalkwiseWeakEquivalences_cylinderProjection_interval C J P) (h.symm ▸ W.id_mem P)⟩

/-- The target of a pointed mapping cylinder is included by a stalkwise
trivial monomorphism. -/
theorem stalkwiseTrivialMonomorphisms_mappingCylinderTarget (f : X ⟶ Y) :
    stalkwiseTrivialMonomorphisms C J (mappingCylinderTarget f) :=
  stalkwiseTrivialMonomorphisms_of_isPushout C J (IsPushout.of_hasPushout _ _)
    (stalkwiseTrivialMonomorphisms_cylinderSection_interval J X 0)

/-- The mapping-cylinder projection is a stalkwise weak equivalence. -/
theorem stalkwiseWeakEquivalences_mappingCylinderProjection (f : X ⟶ Y) :
    stalkwiseWeakEquivalences C J (mappingCylinderProjection f) := by
  let W := stalkwiseWeakEquivalences.{w} C J
  exact W.of_precomp (mappingCylinderTarget f) (mappingCylinderProjection f)
    (stalkwiseTrivialMonomorphisms_mappingCylinderTarget J f).2
    ((mappingCylinderTarget_projection f).symm ▸ W.id_mem Y)

/-- If the given map is a stalkwise weak equivalence, so is the
other endpoint inclusion into its mapping cylinder. -/
theorem stalkwiseWeakEquivalences_mappingCylinderSource {f : X ⟶ Y}
    (hf : stalkwiseWeakEquivalences C J f) :
    stalkwiseWeakEquivalences C J (mappingCylinderSource f) := by
  let W := stalkwiseWeakEquivalences.{w} C J
  exact W.of_postcomp (mappingCylinderSource f) (mappingCylinderProjection f)
    (stalkwiseWeakEquivalences_mappingCylinderProjection J f)
    ((mappingCylinderSource_projection f).symm ▸ hf)

/-- The actual source inclusion of a weak map is a stalkwise trivial
monomorphism. -/
theorem stalkwiseTrivialMonomorphisms_mappingCylinderSource {f : X ⟶ Y}
    (hf : stalkwiseWeakEquivalences C J f) :
    stalkwiseTrivialMonomorphisms C J (mappingCylinderSource f) :=
  ⟨mono_mappingCylinderSource f, stalkwiseWeakEquivalences_mappingCylinderSource J hf⟩

end CategoryTheory.PointedSimplicialPresheaf
