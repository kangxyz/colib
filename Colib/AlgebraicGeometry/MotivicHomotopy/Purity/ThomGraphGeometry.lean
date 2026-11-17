/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Gysin.DiagonalGeometry
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.AffineSpaceProduct
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.Support
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.SupportedGraphDescent
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.SupportProduct

/-! # The graph of a supported projection -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open SmoothSite Contraction

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}}

/-- The graph of the structure morphism of the pair with its actual product maps. -/
def pairProductGraph {A V Y : SmoothSite S} (j : A ⟶ V) (p : V ⟶ Y) :
    Arrow.mk j ⟶ (parameterProduct Y).mapArrow.obj (Arrow.mk j) :=
  Arrow.homMk' (productGraph (j ≫ p)) (productGraph p) (by
    change productGraph (j ≫ p) ≫ productMap j (𝟙 Y) = j ≫ productGraph p
    apply product_hom_ext <;> simp [productGraph])

end AlgebraicGeometry.Scheme.SmoothSite

namespace AlgebraicGeometry.MotivicHomotopy

/-- The restriction graph in the original ambient scheme is the graph into the restricted
ambient scheme followed by its open inclusion in the first factor. -/
theorem productGraph_preimageOpenMap_comp_productMap {S : Scheme.{u}} [IsNoetherian S]
    {V Z : SmoothSite S} (p : V ⟶ Z) (W : Z.left.Opens) :
    productGraph (preimageOpenMap Z p W) ≫
        SmoothSite.productMap (openInclusion V (p.left ⁻¹ᵁ W)) (𝟙 ((opensFunctor Z).obj W)) =
      productLift (openInclusion V (p.left ⁻¹ᵁ W)) (preimageOpenMap Z p W) := by
  let U : SmoothSite S := (opensFunctor V).obj (p.left ⁻¹ᵁ W)
  let Y : SmoothSite S := (opensFunctor Z).obj W
  let a : U ⟶ V := openInclusion V (p.left ⁻¹ᵁ W)
  let b : U ⟶ Y := preimageOpenMap Z p W
  change productGraph b ≫ SmoothSite.productMap a (𝟙 Y) = productLift a b
  apply product_hom_ext (W := U) (X := V) (Y := Y)
  · have hm : SmoothSite.productMap a (𝟙 Y) ≫ productFst V Y = productFst U Y ≫ a :=
      SmoothSite.productMap_fst a (𝟙 Y)
    have hg : productGraph b ≫ productFst U Y = 𝟙 U :=
      productLift_fst (𝟙 U) b
    calc
      _ = productGraph b ≫ (productFst U Y ≫ a) :=
        (Category.assoc _ _ _).trans (congrArg (productGraph b ≫ ·) hm)
      _ = (productGraph b ≫ productFst U Y) ≫ a := (Category.assoc _ _ _).symm
      _ = 𝟙 U ≫ a := congrArg (· ≫ a) hg
      _ = a := Category.id_comp a
      _ = _ := (productLift_fst a b).symm
  · have hm : SmoothSite.productMap a (𝟙 Y) ≫ productSnd V Y = productSnd U Y ≫ 𝟙 Y :=
      SmoothSite.productMap_snd a (𝟙 Y)
    have hg : productGraph b ≫ productSnd U Y = b := productLift_snd (𝟙 U) b
    calc
      _ = productGraph b ≫ (productSnd U Y ≫ 𝟙 Y) :=
        (Category.assoc _ _ _).trans (congrArg (productGraph b ≫ ·) hm)
      _ = (productGraph b ≫ productSnd U Y) ≫ 𝟙 Y := (Category.assoc _ _ _).symm
      _ = b ≫ 𝟙 Y := congrArg (· ≫ 𝟙 Y) hg
      _ = b := Category.comp_id b
      _ = _ := (productLift_snd a b).symm

/-- At the top open, applying its inclusion in the second factor of the restricted graph
gives the original graph precomposed with the ambient open inclusion. -/
theorem openRestrictionProductGraph_top_comp_productMap {S : Scheme.{u}} [IsNoetherian S]
    {V Z : SmoothSite S} (p : V ⟶ Z) :
    openRestrictionProductGraph p ⊤ ≫ SmoothSite.productMap (𝟙 V) (openInclusion Z ⊤) =
      openInclusion V (p.left ⁻¹ᵁ (⊤ : Z.left.Opens)) ≫ productGraph p := by
  let U : SmoothSite S := (opensFunctor V).obj (p.left ⁻¹ᵁ (⊤ : Z.left.Opens))
  let Y : SmoothSite S := (opensFunctor Z).obj (⊤ : Z.left.Opens)
  let a : U ⟶ V := openInclusion V (p.left ⁻¹ᵁ (⊤ : Z.left.Opens))
  let b : U ⟶ Y := preimageOpenMap Z p ⊤
  let c : Y ⟶ Z := openInclusion Z ⊤
  have hb : b ≫ c = a ≫ p :=
    restrictedOpenMap_comp_openInclusion Z p ⊤ (p.left ⁻¹ᵁ (⊤ : Z.left.Opens)) le_rfl
  change productLift a b ≫ SmoothSite.productMap (𝟙 V) c = a ≫ productGraph p
  apply product_hom_ext (W := U) (X := V) (Y := Z)
  · have hm : SmoothSite.productMap (𝟙 V) c ≫ productFst V Z = productFst V Y ≫ 𝟙 V :=
      SmoothSite.productMap_fst (𝟙 V) c
    have hg : productGraph p ≫ productFst V Z = 𝟙 V := productLift_fst (𝟙 V) p
    calc
      _ = productLift a b ≫ (productFst V Y ≫ 𝟙 V) :=
        (Category.assoc _ _ _).trans (congrArg (productLift a b ≫ ·) hm)
      _ = (productLift a b ≫ productFst V Y) ≫ 𝟙 V := (Category.assoc _ _ _).symm
      _ = a ≫ 𝟙 V := congrArg (· ≫ 𝟙 V) (productLift_fst a b)
      _ = a ≫ (productGraph p ≫ productFst V Z) := congrArg (a ≫ ·) hg.symm
      _ = _ := (Category.assoc _ _ _).symm
  · have hm : SmoothSite.productMap (𝟙 V) c ≫ productSnd V Z = productSnd V Y ≫ c :=
      SmoothSite.productMap_snd (𝟙 V) c
    have hg : productGraph p ≫ productSnd V Z = p := productLift_snd (𝟙 V) p
    calc
      _ = productLift a b ≫ (productSnd V Y ≫ c) :=
        (Category.assoc _ _ _).trans (congrArg (productLift a b ≫ ·) hm)
      _ = (productLift a b ≫ productSnd V Y) ≫ c := (Category.assoc _ _ _).symm
      _ = b ≫ c := congrArg (· ≫ c) (productLift_snd a b)
      _ = a ≫ p := hb
      _ = a ≫ (productGraph p ≫ productSnd V Z) := congrArg (a ≫ ·) hg.symm
      _ = _ := (Category.assoc _ _ _).symm

variable {k : Type u} [Field k]

local notation "Sm" => SmoothSite (Spec (CommRingCat.of k))
local notation "B" => base (Spec (CommRingCat.of k))

/-- A map of open pairs over a fixed smooth parameter commutes with their original graphs. -/
theorem pairProductGraph_naturality {A V A' V' Y : Sm}
    {j : A ⟶ V} {j' : A' ⟶ V'} [IsOpenImmersion j'.left]
    (f : Arrow.mk j ⟶ Arrow.mk j') (p : V ⟶ Y) (p' : V' ⟶ Y) (h : f.right ≫ p' = p) :
    f ≫ pairProductGraph j' p' =
      pairProductGraph j p ≫ (parameterProduct Y).mapArrow.map f := by
  let : IsOpenImmersion ((parameterProduct Y).map (Arrow.mk j').hom).left :=
    parameterProduct_map_isOpenImmersion Y j'
  apply openPairArrowMap_eq_of_right (f' := (parameterProduct Y).map (Arrow.mk j').hom)
  change f.right ≫ productGraph p' = productGraph p ≫ SmoothSite.productMap f.right (𝟙 Y)
  apply product_hom_ext <;> simp [productGraph, Category.assoc, h]

/-- In affine coordinates the graph followed by the map to the fixed affine space
is the original isomorphism of the product pair. -/
theorem affineSpacePairProductGraph_eq (Y : Sm) (n : ℕ) :
    pairProductGraph (closedPairOpenInclusion (relativeAffineSpaceZeroSection Y n).left)
        (affineSpaceProjection Y n) ≫
      (parameterProduct Y).mapArrow.map (closedSupportArrowMap
        (affineSpaceOrigin_isPullback (toBase Y) n)) =
    (closedSupportArrowIso (j := supportedProductInclusion (relativeAffineSpaceZeroSection B n) Y)
      (affineSpaceProductIso Y n) (baseProductLeftIso Y).symm
      (affineSpaceProductIso_origin Y n)).hom ≫
      (supportedProductComplementArrowIso (relativeAffineSpaceZeroSection B n) Y).inv := by
  let j₀ := closedPairOpenInclusion (relativeAffineSpaceZeroSection B n).left
  let : IsOpenImmersion ((parameterProduct Y).map (Arrow.mk j₀).hom).left :=
    parameterProduct_map_isOpenImmersion Y j₀
  apply openPairArrowMap_eq_of_right (f' := (parameterProduct Y).map (Arrow.mk j₀).hom)
  change productGraph (affineSpaceProjection Y n) ≫
      SmoothSite.productMap (affineSpaceObjectMap (toBase Y) n) (𝟙 Y) =
    (affineSpaceProductIso Y n).hom ≫ 𝟙 _
  rw [Category.comp_id]
  apply product_hom_ext
  · simp [productGraph, Category.assoc]
  · simp [productGraph, Category.assoc]

end AlgebraicGeometry.MotivicHomotopy
