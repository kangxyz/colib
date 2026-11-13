/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.GroupSchemes
public import Colib.AlgebraicGeometry.Sites.Smooth.Products

/-!
# Retaining both torus coordinates of a power-cut support

The original source torus can be placed on the target side of the
relative product while the source base stays in place. The product
isomorphism retains both original coordinates, including their maps
under a source change.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme SmoothSite

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Gₘ" => SmoothSite.multiplicativeGroupObject Sₖ
local notation "G(" X ")" => product X Gₘ

/-- The original target torus and the retained source torus over the target. -/
abbrev torusPowerCutRetainedTarget (Y : SmoothSite Sₖ) : SmoothSite Sₖ :=
  product (G(Y)) Gₘ

local notation "R(" Y ")" => torusPowerCutRetainedTarget k Y

/-- The original ambient product, with the source torus moved to the target. -/
def torusPowerCutAmbientIso (X Y : SmoothSite Sₖ) :
    product (G(X)) (G(Y)) ≅ product X (R(Y)) where
  hom := productLift
    (productFst (G(X)) (G(Y)) ≫ productFst X Gₘ)
    (productLift (productSnd (G(X)) (G(Y)))
      (productFst (G(X)) (G(Y)) ≫ productSnd X Gₘ))
  inv := productLift
    (productLift (productFst X (R(Y)))
      (productSnd X (R(Y)) ≫ productSnd (G(Y)) Gₘ))
    (productSnd X (R(Y)) ≫ productFst (G(Y)) Gₘ)
  hom_inv_id := by
    apply product_hom_ext
    · apply product_hom_ext <;> simp [Category.assoc]
    · simp [Category.assoc]
  inv_hom_id := by
    apply product_hom_ext
    · simp [Category.assoc]
    · apply product_hom_ext <;> simp [Category.assoc]

/-- The source base projection is the original projection through the source torus. -/
@[reassoc (attr := simp)]
theorem torusPowerCutAmbientIso_hom_source (X Y : SmoothSite Sₖ) :
    (torusPowerCutAmbientIso k X Y).hom ≫ productFst X (R(Y)) =
      productFst (G(X)) (G(Y)) ≫ productFst X Gₘ := by
  simp [torusPowerCutAmbientIso]

/-- The original target projection retains the target torus. -/
@[reassoc (attr := simp)]
theorem torusPowerCutAmbientIso_hom_target (X Y : SmoothSite Sₖ) :
    (torusPowerCutAmbientIso k X Y).hom ≫ productSnd X (R(Y)) ≫ productFst (G(Y)) Gₘ =
      productSnd (G(X)) (G(Y)) := by
  simp [torusPowerCutAmbientIso]

/-- The last retained projection is the original source torus. -/
@[reassoc (attr := simp)]
theorem torusPowerCutAmbientIso_hom_torus (X Y : SmoothSite Sₖ) :
    (torusPowerCutAmbientIso k X Y).hom ≫ productSnd X (R(Y)) ≫ productSnd (G(Y)) Gₘ =
      productFst (G(X)) (G(Y)) ≫ productSnd X Gₘ := by
  simp [torusPowerCutAmbientIso]

/-- The retained product is natural for changes of the original source base. -/
theorem torusPowerCutAmbientIso_naturality {X' X : SmoothSite Sₖ}
    (Y : SmoothSite Sₖ) (φ : X' ⟶ X) :
    productMap (productMap φ (𝟙 Gₘ)) (𝟙 (G(Y))) ≫ (torusPowerCutAmbientIso k X Y).hom =
      (torusPowerCutAmbientIso k X' Y).hom ≫ productMap φ (𝟙 (R(Y))) := by
  apply product_hom_ext
  · simp [Category.assoc]
  · apply product_hom_ext <;> simp [Category.assoc]

/-- The same isomorphism on the literal two schemes carrying the cycles. -/
def torusPowerCutAmbientSchemeIso (X Y : SmoothSite Sₖ) :
    pullback (G(X)).hom (G(Y)).hom ≅ pullback X.hom (R(Y)).hom :=
  (SmoothSite.forgetScheme Sₖ).mapIso (torusPowerCutAmbientIso k X Y)

end AlgebraicGeometry.Cor
