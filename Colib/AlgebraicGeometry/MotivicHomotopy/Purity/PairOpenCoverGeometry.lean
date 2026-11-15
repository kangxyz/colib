/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Cohomology.GenericOpen
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square
import Colib.AlgebraicGeometry.Sites.Smooth.Cartier.PunctureComparison

/-! # Restricting smooth schemes to the opens of a binary cover -/

public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.MotivicHomotopy

section Opens

open AlgebraicGeometry.Scheme.SmoothSite

variable {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsNoetherian S]
  (X : SmoothSite S) (U V : X.left.Opens)

/-- Two literal opens cover their union through the original inclusion maps. -/
@[expose] def openUnionCoverSquare : Square (SmoothSite S) where
  f₁₂ := (opensFunctor X).map (homOfLE (inf_le_left : U ⊓ V ≤ U))
  f₁₃ := (opensFunctor X).map (homOfLE (inf_le_right : U ⊓ V ≤ V))
  f₂₄ := (opensFunctor X).map (homOfLE (le_sup_left : U ≤ U ⊔ V))
  f₃₄ := (opensFunctor X).map (homOfLE (le_sup_right : V ≤ U ⊔ V))
  fac := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl

/-- The overlap in the union cover is the literal intersection. -/
theorem openUnionCoverSquare_isPullback : (openUnionCoverSquare X U V).IsPullback := by
  apply IsPullback.of_map_of_faithful (forgetScheme S)
  exact isPullback_opens_inf_le (le_sup_left : U ≤ U ⊔ V) (le_sup_right : V ≤ U ⊔ V)

instance openUnionCoverSquare_f₂₄_isOpenImmersion :
    AlgebraicGeometry.IsOpenImmersion (openUnionCoverSquare X U V).f₂₄.left :=
  inferInstanceAs (AlgebraicGeometry.IsOpenImmersion (X.left.homOfLE (le_sup_left : U ≤ U ⊔ V)))

instance openUnionCoverSquare_f₃₄_isOpenImmersion :
    AlgebraicGeometry.IsOpenImmersion (openUnionCoverSquare X U V).f₃₄.left :=
  inferInstanceAs
    (AlgebraicGeometry.IsOpenImmersion (X.left.homOfLE (le_sup_right : V ≤ U ⊔ V)))

/-- The images of the two chart inclusions exhaust the literal union. -/
theorem openUnionCoverSquare_range_cover :
    Set.range (openUnionCoverSquare X U V).f₂₄.left ∪
      Set.range (openUnionCoverSquare X U V).f₃₄.left = Set.univ := by
  ext x
  change x ∈ Set.range (X.left.homOfLE (le_sup_left : U ≤ U ⊔ V)) ∪
      Set.range (X.left.homOfLE (le_sup_right : V ≤ U ⊔ V)) ↔ _
  constructor
  · intro _
    trivial
  · intro _
    rcases x.property with hx | hx
    · exact Or.inl ⟨⟨x.val, hx⟩, Subtype.ext (X.left.homOfLE_apply _ _)⟩
    · exact Or.inr ⟨⟨x.val, hx⟩, Subtype.ext (X.left.homOfLE_apply _ _)⟩

variable {Y : SmoothSite S} (f : Y ⟶ X)

/-- The original morphism restricted between specified opens. -/
@[expose] def restrictedOpenMap (W : X.left.Opens) (T : Y.left.Opens)
    (e : T ≤ f.left ⁻¹ᵁ W) :
    (opensFunctor Y).obj T ⟶ (opensFunctor X).obj W :=
  homMk (f.left.resLE W T e) (by
    change f.left.resLE W T e ≫ W.ι ≫ X.hom = T.ι ≫ Y.hom
    rw [← Category.assoc, AlgebraicGeometry.Scheme.Hom.resLE_comp_ι,
      Category.assoc, MorphismProperty.Over.w f])

/-- The restriction commutes with the actual inclusions into the ambient schemes. -/
theorem restrictedOpenMap_comp_openInclusion (W : X.left.Opens) (T : Y.left.Opens)
    (e : T ≤ f.left ⁻¹ᵁ W) :
    restrictedOpenMap X f W T e ≫ openInclusion X W = openInclusion Y T ≫ f := by
  apply MorphismProperty.Over.Hom.ext
  exact AlgebraicGeometry.Scheme.Hom.resLE_comp_ι f.left e

/-- The restriction to specified opens commutes with the actual inclusions. -/
theorem restrictedOpenMap_naturality {W W' : X.left.Opens} {T T' : Y.left.Opens}
    (h : W ≤ W') (g : T ≤ T') (e : T ≤ f.left ⁻¹ᵁ W) (e' : T' ≤ f.left ⁻¹ᵁ W') :
    (opensFunctor Y).map (homOfLE g) ≫ restrictedOpenMap X f W' T' e' =
      restrictedOpenMap X f W T e ≫ (opensFunctor X).map (homOfLE h) := by
  apply MorphismProperty.Over.Hom.ext
  apply (cancel_mono W'.ι).1
  change (Y.left.homOfLE g ≫ f.left.resLE W' T' e') ≫ W'.ι =
    (f.left.resLE W T e ≫ X.left.homOfLE h) ≫ W'.ι
  simp only [Category.assoc, AlgebraicGeometry.Scheme.Hom.resLE_comp_ι,
    AlgebraicGeometry.Scheme.homOfLE_ι, AlgebraicGeometry.Scheme.homOfLE_ι_assoc]

/-- The original morphism restricted to the inverse image of a specified open. -/
abbrev preimageOpenMap (W : X.left.Opens) :
    (opensFunctor Y).obj (f.left ⁻¹ᵁ W) ⟶ (opensFunctor X).obj W :=
  restrictedOpenMap X f W (f.left ⁻¹ᵁ W) le_rfl

/-- Preimage and inclusion form a commuting square for the literal open restrictions. -/
theorem preimageOpenMap_naturality {W W' : X.left.Opens} (h : W ≤ W') :
    (opensFunctor Y).map (homOfLE (f.left.preimage_mono h)) ≫ preimageOpenMap X f W' =
      preimageOpenMap X f W ≫ (opensFunctor X).map (homOfLE h) :=
  restrictedOpenMap_naturality X f h (f.left.preimage_mono h) le_rfl le_rfl

/-- A morphism of the two literal union covers from the inverse-image cover. -/
@[expose] def preimageOpenUnionCoverMap :
    openUnionCoverSquare Y (f.left ⁻¹ᵁ U) (f.left ⁻¹ᵁ V) ⟶ openUnionCoverSquare X U V :=
  { τ₁ := preimageOpenMap X f (U ⊓ V)
    τ₂ := preimageOpenMap X f U
    τ₃ := preimageOpenMap X f V
    τ₄ := preimageOpenMap X f (U ⊔ V)
    comm₁₂ := preimageOpenMap_naturality X f inf_le_left
    comm₁₃ := preimageOpenMap_naturality X f inf_le_right
    comm₂₄ := preimageOpenMap_naturality X f le_sup_left
    comm₃₄ := preimageOpenMap_naturality X f le_sup_right }

instance preimageOpenMap_isOpenImmersion [AlgebraicGeometry.IsOpenImmersion f.left]
    (W : X.left.Opens) : AlgebraicGeometry.IsOpenImmersion (preimageOpenMap X f W).left := by
  change AlgebraicGeometry.IsOpenImmersion (f.left.resLE W (f.left ⁻¹ᵁ W) le_rfl)
  rw [AlgebraicGeometry.Scheme.Hom.resLE_eq_morphismRestrict]
  exact MorphismProperty.of_isPullback (isPullback_morphismRestrict f.left W).flip inferInstance

end Opens

end AlgebraicGeometry.MotivicHomotopy
