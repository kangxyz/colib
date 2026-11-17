/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.PairOpenCover
public import Colib.AlgebraicGeometry.Sites.Smooth.Cohomology.GenericOpen
public import Colib.AlgebraicGeometry.Sites.Smooth.Products
import Colib.AlgebraicGeometry.Sites.Smooth.Cartier.NativeSections
import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Pullbacks
import Colib.AlgebraicGeometry.Scheme.CartesianRange
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Square

/-!
# The graph on binary covers of relative pairs

The fixed open pair is multiplied by the four corners of the base open cover.
Graphs of the restrictions map the original relative cover into this product cover.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open SmoothSite

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable {S : AlgebraicGeometry.Scheme.{u}}

/-- Product with a fixed ambient scheme on the left. -/
def smoothCoverLeftProduct (X : SmoothSite S) : SmoothSite S ⥤ SmoothSite S where
  obj Y := product X Y
  map f := SmoothSite.productMap (𝟙 X) f
  map_id _ := productMap_id _ _
  map_comp f g := by rw [← productMap_comp, Category.id_comp]

/-- The literal map of a left product induced by a map in its fixed factor. -/
def smoothCoverLeftProductMap {U V : SmoothSite S} (j : U ⟶ V) :
    smoothCoverLeftProduct U ⟶ smoothCoverLeftProduct V where
  app X := SmoothSite.productMap j (𝟙 X)
  naturality := by
    intro X Y f
    change SmoothSite.productMap (𝟙 U) f ≫ SmoothSite.productMap j (𝟙 Y) =
      SmoothSite.productMap j (𝟙 X) ≫ SmoothSite.productMap (𝟙 V) f
    rw [← productMap_comp, ← productMap_comp]
    simp only [Category.id_comp, Category.comp_id]

/-- The four original product-pair inclusions over the base cover. -/
abbrev smoothPairProductCoverMap {U V : SmoothSite S} (j : U ⟶ V)
    (sq : Square (SmoothSite S)) :
    sq.map (smoothCoverLeftProduct U) ⟶ sq.map (smoothCoverLeftProduct V) :=
  (smoothCoverLeftProductMap j).mapSquare.app sq

/-- The fixed left product preserves the base cover's Cartesian square. -/
theorem smoothCoverLeftProduct_isPullback (X : SmoothSite S) (sq : Square (SmoothSite S))
    (h : sq.IsPullback) [AlgebraicGeometry.IsOpenImmersion sq.f₂₄.left] :
    (sq.map (smoothCoverLeftProduct X)).IsPullback := by
  let e := SmoothSite.forgetScheme S
  have h₀ : IsPullback sq.f₁₂.left sq.f₁₃.left sq.f₂₄.left sq.f₃₄.left :=
    (SmoothSite.forgetScheme S).map_isPullback h
  have h₁ := (productMap_right_isPullback X sq.f₁₂).paste_vert h₀
  have h₁₃ := (productMap_right_isPullback X sq.f₁₃).w
  have h₂₄ := (productMap_right_isPullback X sq.f₂₄).w
  rw [← h₁₃, ← h₂₄] at h₁
  apply IsPullback.of_map_of_faithful e
  exact h₁.of_bot (congrArg (fun f => f.left) ((sq.map (smoothCoverLeftProduct X)).fac))
    (productMap_right_isPullback X sq.f₃₄)

/-- The two product inclusions cover the product with the union. -/
theorem smoothCoverLeftProduct_range_cover (X : SmoothSite S) (sq : Square (SmoothSite S))
    (h : Set.range sq.f₂₄.left ∪ Set.range sq.f₃₄.left = Set.univ) :
    Set.range (sq.map (smoothCoverLeftProduct X)).f₂₄.left ∪
      Set.range (sq.map (smoothCoverLeftProduct X)).f₃₄.left = Set.univ := by
  change Set.range (SmoothSite.productMap (𝟙 X) sq.f₂₄).left ∪
    Set.range (SmoothSite.productMap (𝟙 X) sq.f₃₄).left = Set.univ
  rw [range_fst_of_isPullback (productMap_right_isPullback X sq.f₂₄),
    range_fst_of_isPullback (productMap_right_isPullback X sq.f₃₄), ← Set.preimage_union,
    h, Set.preimage_univ]

/-- The fixed product of an open chart remains an open immersion. -/
instance smoothCoverLeftProduct_map_isOpenImmersion (X : SmoothSite S)
    {Y Y' : SmoothSite S} (f : Y ⟶ Y') [AlgebraicGeometry.IsOpenImmersion f.left] :
    AlgebraicGeometry.IsOpenImmersion ((smoothCoverLeftProduct X).map f).left :=
  MorphismProperty.of_isPullback (productMap_right_isPullback X f).flip inferInstance

/-- The product pair keeps the given open immersion in the first variable. -/
instance smoothPairProductCoverMap_component_isOpenImmersion {U V : SmoothSite S}
    (j : U ⟶ V) [AlgebraicGeometry.IsOpenImmersion j.left] (X : SmoothSite S) :
    AlgebraicGeometry.IsOpenImmersion (SmoothSite.productMap j (𝟙 X)).left := by
  have h : IsPullback (SmoothSite.productMap j (𝟙 X)).left (productFst U X).left
      (productFst V X).left j.left := by
    apply IsPullback.of_right (h₁₂ := (productSnd V X).left)
      (h₂₂ := V.hom) (v₁₃ := X.hom)
    · have e := congrArg (fun f => f.left) (productMap_snd j (𝟙 X))
      change (SmoothSite.productMap j (𝟙 X)).left ≫ (productSnd V X).left =
        (productSnd U X).left ≫ 𝟙 X.left at e
      rw [e, Category.comp_id, MorphismProperty.Over.w j]
      exact (IsPullback.of_hasPullback U.hom X.hom).flip
    · exact congrArg (fun f => f.left) (productMap_fst j (𝟙 X))
    · exact (IsPullback.of_hasPullback V.hom X.hom).flip
  exact MorphismProperty.of_isPullback h.flip inferInstance

section Transfer

open SheafWithTransfers

variable (k : Type u) [Field k]

local notation "Sm" => SmoothSite (Spec (CommRingCat.of k))

/-- The signed quotient row of the actual product pairs is short exact
on a cover by two opens of the parameter scheme. -/
theorem transferPairProductOpenCoverSequence_shortExact {U V : Sm}
    (j : U ⟶ V) [AlgebraicGeometry.IsOpenImmersion j.left] (sq : Square Sm) (h : sq.IsPullback)
    [AlgebraicGeometry.IsOpenImmersion sq.f₂₄.left]
    [AlgebraicGeometry.IsOpenImmersion sq.f₃₄.left]
    (hc : Set.range sq.f₂₄.left ∪ Set.range sq.f₃₄.left = Set.univ) :
    (transferPairOpenCoverSequence k (smoothPairProductCoverMap j sq)).ShortExact := by
  let : AlgebraicGeometry.IsOpenImmersion (smoothPairProductCoverMap j sq).τ₁.left :=
    smoothPairProductCoverMap_component_isOpenImmersion j sq.X₁
  let : AlgebraicGeometry.IsOpenImmersion (smoothPairProductCoverMap j sq).τ₂.left :=
    smoothPairProductCoverMap_component_isOpenImmersion j sq.X₂
  let : AlgebraicGeometry.IsOpenImmersion (smoothPairProductCoverMap j sq).τ₃.left :=
    smoothPairProductCoverMap_component_isOpenImmersion j sq.X₃
  let : AlgebraicGeometry.IsOpenImmersion (smoothPairProductCoverMap j sq).τ₄.left :=
    smoothPairProductCoverMap_component_isOpenImmersion j sq.X₄
  let : AlgebraicGeometry.IsOpenImmersion (sq.map (smoothCoverLeftProduct U)).f₂₄.left :=
    smoothCoverLeftProduct_map_isOpenImmersion U sq.f₂₄
  let : AlgebraicGeometry.IsOpenImmersion (sq.map (smoothCoverLeftProduct U)).f₃₄.left :=
    smoothCoverLeftProduct_map_isOpenImmersion U sq.f₃₄
  let : AlgebraicGeometry.IsOpenImmersion (sq.map (smoothCoverLeftProduct V)).f₂₄.left :=
    smoothCoverLeftProduct_map_isOpenImmersion V sq.f₂₄
  let : AlgebraicGeometry.IsOpenImmersion (sq.map (smoothCoverLeftProduct V)).f₃₄.left :=
    smoothCoverLeftProduct_map_isOpenImmersion V sq.f₃₄
  exact transferPairOpenCoverSequence_shortExact k (smoothPairProductCoverMap j sq)
    (smoothCoverLeftProduct_isPullback U sq h) (smoothCoverLeftProduct_isPullback V sq h)
    (smoothCoverLeftProduct_range_cover U sq hc) (smoothCoverLeftProduct_range_cover V sq hc)

end Transfer

section Graph

variable [AlgebraicGeometry.IsNoetherian S] {B : SmoothSite S}

/-- The graph of the restricted map to an open chart, with the first
coordinate taking values in the fixed original ambient scheme. -/
def openRestrictionProductGraph {X : SmoothSite S} (p : X ⟶ B) (W : B.left.Opens) :
    (opensFunctor X).obj (p.left ⁻¹ᵁ W) ⟶ product X ((opensFunctor B).obj W) :=
  productLift (openInclusion X (p.left ⁻¹ᵁ W)) (preimageOpenMap B p W)

/-- The actual graph restrictions commute with the original inclusions of the base opens. -/
theorem openRestrictionProductGraph_naturality {X : SmoothSite S} (p : X ⟶ B)
    {W T : B.left.Opens} (h : W ≤ T) :
    (opensFunctor X).map (homOfLE (p.left.preimage_mono h)) ≫ openRestrictionProductGraph p T =
      openRestrictionProductGraph p W ≫
        (smoothCoverLeftProduct X).map ((opensFunctor B).map (homOfLE h)) := by
  apply product_hom_ext
  · simp only [openRestrictionProductGraph, Category.assoc, smoothCoverLeftProduct]
    rw [productMap_fst, Category.comp_id, productLift_fst, productLift_fst]
    apply MorphismProperty.Over.Hom.ext
    exact Scheme.homOfLE_ι _ (p.left.preimage_mono h)
  · simpa [openRestrictionProductGraph, smoothCoverLeftProduct] using
      preimageOpenMap_naturality B p h

/-- The four graph restrictions are a map of the actual two-open cover squares. -/
def openRestrictionProductGraphCoverMap {X : SmoothSite S} (p : X ⟶ B) (W T : B.left.Opens) :
    openUnionCoverSquare X (p.left ⁻¹ᵁ W) (p.left ⁻¹ᵁ T) ⟶
      (openUnionCoverSquare B W T).map (smoothCoverLeftProduct X) where
  τ₁ := openRestrictionProductGraph p (W ⊓ T)
  τ₂ := openRestrictionProductGraph p W
  τ₃ := openRestrictionProductGraph p T
  τ₄ := openRestrictionProductGraph p (W ⊔ T)
  comm₁₂ := openRestrictionProductGraph_naturality p inf_le_left
  comm₁₃ := openRestrictionProductGraph_naturality p inf_le_right
  comm₂₄ := openRestrictionProductGraph_naturality p le_sup_left
  comm₃₄ := openRestrictionProductGraph_naturality p le_sup_right

/-- The complement graph uses the literal iterated inverse-image open. -/
def openRestrictionComplementProductGraph {U X : SmoothSite S}
    (p : X ⟶ B) (j : U ⟶ X) (W : B.left.Opens) :
    (opensFunctor U).obj (j.left ⁻¹ᵁ (p.left ⁻¹ᵁ W)) ⟶
      product U ((opensFunctor B).obj W) :=
  let a := j.left ⁻¹ᵁ (p.left ⁻¹ᵁ W)
  productLift (openInclusion U a)
    (restrictedOpenMap B (j ≫ p) W a (by
      change j.left ⁻¹ᵁ (p.left ⁻¹ᵁ W) ≤ (j.left ≫ p.left) ⁻¹ᵁ W
      rw [Scheme.Hom.comp_preimage]))

/-- The graph on the complement commutes with the original open immersion. -/
theorem openRestrictionProductGraph_pair_comm {U X : SmoothSite S}
    (p : X ⟶ B) (j : U ⟶ X) (W : B.left.Opens) :
    preimageOpenMap X j (p.left ⁻¹ᵁ W) ≫ openRestrictionProductGraph p W =
      openRestrictionComplementProductGraph p j W ≫
        SmoothSite.productMap j (𝟙 ((opensFunctor B).obj W)) := by
  apply product_hom_ext
  · simp only [openRestrictionProductGraph, openRestrictionComplementProductGraph, Category.assoc]
    rw [productMap_fst, ← Category.assoc _ (productFst _ _) j,
      productLift_fst, productLift_fst]
    exact restrictedOpenMap_comp_openInclusion X j (p.left ⁻¹ᵁ W)
        (j.left ⁻¹ᵁ (p.left ⁻¹ᵁ W)) le_rfl
  · let : Mono (openInclusion B W) := (SmoothSite.forgetScheme S).mono_of_mono_map
      (inferInstanceAs (Mono W.ι))
    apply (cancel_mono (openInclusion B W)).1
    simp only [openRestrictionProductGraph, openRestrictionComplementProductGraph, Category.assoc]
    rw [productMap_snd_assoc, Category.id_comp, productLift_snd_assoc, productLift_snd_assoc]
    rw [restrictedOpenMap_comp_openInclusion, ← Category.assoc,
      restrictedOpenMap_comp_openInclusion, Category.assoc, restrictedOpenMap_comp_openInclusion]

/-- The graph of the pair restriction, with both actual product coordinates. -/
def openRestrictionProductGraphArrowMap {U X : SmoothSite S}
    (p : X ⟶ B) (j : U ⟶ X) (W : B.left.Opens) :
    Arrow.mk (preimageOpenMap X j (p.left ⁻¹ᵁ W)) ⟶
      Arrow.mk (SmoothSite.productMap j (𝟙 ((opensFunctor B).obj W))) :=
  Arrow.homMk' (openRestrictionComplementProductGraph p j W) (openRestrictionProductGraph p W)
    (openRestrictionProductGraph_pair_comm p j W).symm

/-- Restricting the complement graph commutes with the original open inclusions. -/
theorem openRestrictionComplementProductGraph_naturality {U X : SmoothSite S}
    (p : X ⟶ B) (j : U ⟶ X) {W T : B.left.Opens} (h : W ≤ T) :
    (opensFunctor U).map (homOfLE (j.left.preimage_mono (p.left.preimage_mono h))) ≫
        openRestrictionComplementProductGraph p j T =
      openRestrictionComplementProductGraph p j W ≫
        (smoothCoverLeftProduct U).map ((opensFunctor B).map (homOfLE h)) := by
  let h₀ := j.left.preimage_mono (p.left.preimage_mono h)
  apply product_hom_ext
  · simp only [openRestrictionComplementProductGraph, Category.assoc, smoothCoverLeftProduct]
    rw [productMap_fst, Category.comp_id, productLift_fst, productLift_fst]
    apply MorphismProperty.Over.Hom.ext
    exact Scheme.homOfLE_ι _ h₀
  · let : Mono (openInclusion B T) := (SmoothSite.forgetScheme S).mono_of_mono_map
      (inferInstanceAs (Mono T.ι))
    apply (cancel_mono (openInclusion B T)).1
    simp only [openRestrictionComplementProductGraph, Category.assoc, smoothCoverLeftProduct]
    rw [productMap_snd_assoc, productLift_snd_assoc, productLift_snd_assoc,
      restrictedOpenMap_comp_openInclusion]
    have hc : (opensFunctor B).map (homOfLE h) ≫ openInclusion B T = openInclusion B W := by
      apply MorphismProperty.Over.Hom.ext
      exact Scheme.homOfLE_ι _ h
    rw [hc, restrictedOpenMap_comp_openInclusion, ← Category.assoc]
    congr 1
    apply MorphismProperty.Over.Hom.ext
    exact Scheme.homOfLE_ι _ h₀

/-- The graph on the four open complements of a binary relative cover. -/
def openRestrictionComplementProductGraphCoverMap {U X : SmoothSite S}
    (p : X ⟶ B) (j : U ⟶ X) (W T : B.left.Opens) :
    openUnionCoverSquare U (j.left ⁻¹ᵁ (p.left ⁻¹ᵁ W))
      (j.left ⁻¹ᵁ (p.left ⁻¹ᵁ T)) ⟶
      (openUnionCoverSquare B W T).map (smoothCoverLeftProduct U) where
  τ₁ := openRestrictionComplementProductGraph p j (W ⊓ T)
  τ₂ := openRestrictionComplementProductGraph p j W
  τ₃ := openRestrictionComplementProductGraph p j T
  τ₄ := openRestrictionComplementProductGraph p j (W ⊔ T)
  comm₁₂ := openRestrictionComplementProductGraph_naturality p j inf_le_left
  comm₁₃ := openRestrictionComplementProductGraph_naturality p j inf_le_right
  comm₂₄ := openRestrictionComplementProductGraph_naturality p j le_sup_left
  comm₃₄ := openRestrictionComplementProductGraph_naturality p j le_sup_right

/-- The maps of ambient and complement cover squares give the same original pair map
at each of the four vertices. -/
theorem openRestrictionProductGraphCoverMap_pair_comm {U X : SmoothSite S}
    (p : X ⟶ B) (j : U ⟶ X) (W T : B.left.Opens) :
    preimageOpenUnionCoverMap X (p.left ⁻¹ᵁ W) (p.left ⁻¹ᵁ T) j ≫
        openRestrictionProductGraphCoverMap p W T =
      openRestrictionComplementProductGraphCoverMap p j W T ≫
        smoothPairProductCoverMap j (openUnionCoverSquare B W T) := by
  apply Square.Hom.ext
  exacts [openRestrictionProductGraph_pair_comm p j (W ⊓ T),
    openRestrictionProductGraph_pair_comm p j W, openRestrictionProductGraph_pair_comm p j T,
    openRestrictionProductGraph_pair_comm p j (W ⊔ T)]

end Graph

end AlgebraicGeometry.MotivicHomotopy
