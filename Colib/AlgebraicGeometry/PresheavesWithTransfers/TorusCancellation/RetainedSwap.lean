/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.AffineTorusPoints
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.DoubleTorusPencil

/-!
# The swap homotopy on the double torus over any smooth source

The two actual torus coordinates on the original double product pull back
from the affine binary torus. Their projection is flat and the source
coordinate is retained throughout the quadratic construction. The literal
endpoint graphs give the swap and the inverse on the last factor.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NativeTorusPolynomial
open AlgebraicGeometry.Scheme SmoothSite SmoothSite.Contraction
open AlgebraicGeometry.Scheme.SmoothSite.AffineSectionCoordinates

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Gₖ" => multiplicativeGroupObject Sₖ
local notation "Tₖ" => SmoothSite.product Gₖ Gₖ
local notation "γ" => CategoryTheory.Functor.map (Cor.graphFunctor k)

section Coordinates

variable (X : SmoothSite (Spec (CommRingCat.of k)))

local notation "XG" => SmoothSite.product X Gₖ
local notation "D" => SmoothSite.product XG Gₖ

private abbrev doubleTorus_base : D ⟶ X := productFst XG Gₖ ≫ productFst X Gₖ

private abbrev doubleTorus_first : D ⟶ Gₖ := productFst XG Gₖ ≫ productSnd X Gₖ

private abbrev doubleTorus_last : D ⟶ Gₖ := productSnd XG Gₖ

private abbrev doubleTorus_pair : D ⟶ Tₖ :=
  productLift (doubleTorus_first k X) (doubleTorus_last k X)

private def doubleTorus_assocIso : D ≅ SmoothSite.product X Tₖ where
  hom := productLift (doubleTorus_base k X) (doubleTorus_pair k X)
  inv := productLift
    (productLift (productFst X Tₖ) (productSnd X Tₖ ≫ productFst Gₖ Gₖ))
    (productSnd X Tₖ ≫ productSnd Gₖ Gₖ)
  hom_inv_id := by
    apply product_hom_ext
    · apply product_hom_ext <;>
        simp [doubleTorus_base, doubleTorus_pair, doubleTorus_first, Category.assoc]
    · simp [doubleTorus_pair, doubleTorus_last, Category.assoc]
  inv_hom_id := by
    apply product_hom_ext
    · simp [doubleTorus_base, Category.assoc]
    · apply product_hom_ext <;>
        simp [doubleTorus_pair, doubleTorus_first, doubleTorus_last, Category.assoc]

private theorem doubleTorus_pair_flat : Flat (doubleTorus_pair k X).left := by
  let e := doubleTorus_assocIso k X
  let : IsIso e.hom.left :=
    inferInstanceAs (IsIso ((SmoothSite.forgetScheme Sₖ).mapIso e).hom)
  let : Flat (productSnd X Tₖ).left :=
    inferInstanceAs (Flat (pullback.snd X.hom (Tₖ).hom))
  have h : e.hom ≫ productSnd X Tₖ = doubleTorus_pair k X := productLift_snd _ _
  rw [← h]
  exact inferInstanceAs (Flat (e.hom.left ≫ (productSnd X Tₖ).left))

end Coordinates

variable (X : Cor k)

set_option quotPrecheck false in
local notation "X₀" => X.toSmoothSite
local notation "XG" => SmoothSite.product X₀ Gₖ
local notation "D" => SmoothSite.product XG Gₖ
local notation "σ(" a ")" => nativeAffineSection (CommRingCat.of k) D a

/-- The chosen signed homotopy of the native double torus over the original smooth base. -/
@[no_expose]
def torusDoubleSwapHomotopy : Cor.mk (affineLineCylinder.obj D) ⟶ Cor.mk D := by
  let : IsAffine (Tₖ).left := torusBinaryProduct_isAffine (k := k)
  let : IsIntegral (Tₖ).left := torusBinaryProduct_isIntegral (k := k)
  let R := Γ((Tₖ).left, ⊤)
  let : Algebra k R := sectionsAlgebra Tₖ
  let : Algebra.Smooth k R := sections_smooth Tₖ
  let : IsDomain R := IsIntegral.component_integral (⊤ : (Tₖ).left.Opens)
  let : IsNoetherianRing R := sections_isNoetherianRing Tₖ
  let : IsIntegrallyClosed R := sections_isIntegrallyClosed Tₖ
  let e : affineSite k R ≅ Tₖ := affineIso Tₖ
  let j := doubleTorus_pair k X₀ ≫ e.inv
  let p := doubleTorus_base k X₀
  let : Flat (doubleTorus_pair k X₀).left := doubleTorus_pair_flat k X₀
  let : IsIso e.inv.left :=
    inferInstanceAs (IsIso ((SmoothSite.forgetScheme Sₖ).mapIso e).inv)
  let : Flat j.left :=
    inferInstanceAs (Flat ((doubleTorus_pair k X₀).left ≫ e.inv.left))
  let a : Rˣ := affineUnitOfPoint (e.hom ≫ productFst Gₖ Gₖ)
  let b : Rˣ := affineUnitOfPoint (e.hom ≫ productSnd Gₖ Gₖ)
  exact γ (affineLineCylinder.map (productSwapLast X₀ Gₖ Gₖ)) ≫
    reducedDoubleTorusPairGraphSwapHomotopy j p a b

set_option maxHeartbeats 1000000 in
-- The source, affine chart, and projected graph endpoints use the original dependent objects.
/-- The chosen homotopy has the actual swap and outer inverse endpoints. -/
theorem torusDoubleSwapHomotopy_endpoints :
    γ (σ(0)) ≫ torusDoubleSwapHomotopy k X =
        torusDoubleSwap k X ≫ torusDoubleReduction k X ∧
      γ (σ(1)) ≫ torusDoubleSwapHomotopy k X =
        torusDoubleInversion k X ≫ torusDoubleReduction k X := by
  let : IsAffine (Tₖ).left := torusBinaryProduct_isAffine (k := k)
  let : IsIntegral (Tₖ).left := torusBinaryProduct_isIntegral (k := k)
  let R := Γ((Tₖ).left, ⊤)
  let : Algebra k R := sectionsAlgebra Tₖ
  let : Algebra.Smooth k R := sections_smooth Tₖ
  let : IsDomain R := IsIntegral.component_integral (⊤ : (Tₖ).left.Opens)
  let : IsNoetherianRing R := sections_isNoetherianRing Tₖ
  let : IsIntegrallyClosed R := sections_isIntegrallyClosed Tₖ
  let e : affineSite k R ≅ Tₖ := affineIso Tₖ
  let j := doubleTorus_pair k X₀ ≫ e.inv
  let p := doubleTorus_base k X₀
  let : Flat (doubleTorus_pair k X₀).left := doubleTorus_pair_flat k X₀
  let : IsIso e.inv.left :=
    inferInstanceAs (IsIso ((SmoothSite.forgetScheme Sₖ).mapIso e).inv)
  let : Flat j.left :=
    inferInstanceAs (Flat ((doubleTorus_pair k X₀).left ≫ e.inv.left))
  let a : Rˣ := affineUnitOfPoint (e.hom ≫ productFst Gₖ Gₖ)
  let b : Rˣ := affineUnitOfPoint (e.hom ≫ productSnd Gₖ Gₖ)
  let point (c : Rˣ) : affineSite k R ⟶ Gₖ :=
    homMk (nativeAffineTorusPoint (affineSite k R).hom c).left
      (nativeTorusPoint_over (affineSite k R).hom (specGlobalUnit c))
  have ha₀ : point a = e.hom ≫ productFst Gₖ Gₖ := affineUnitOfPoint_recover _
  have hb₀ : point b = e.hom ≫ productSnd Gₖ Gₖ := affineUnitOfPoint_recover _
  have ha : j ≫ point a = doubleTorus_first k X₀ := by
    rw [ha₀]
    simp only [j, Category.assoc, Iso.inv_hom_id_assoc, doubleTorus_pair, productLift_fst]
  have hb : j ≫ point b = doubleTorus_last k X₀ := by
    rw [hb₀]
    simp only [j, Category.assoc, Iso.inv_hom_id_assoc, doubleTorus_pair, productLift_snd]
  have hi : point a⁻¹ = point a ≫ torusInversion Sₖ :=
    (affineUnitPoint_comp_torusInversion (k := k) a).symm
  let s := productSwapLast X₀ Gₖ Gₖ
  let i := SmoothSite.productMap (𝟙 XG) (torusInversion Sₖ)
  have hs : s ≫ s = 𝟙 D := (productSwapLastIso X₀ Gₖ Gₖ).hom_inv_id
  have h₀ : productLift (productLift p (j ≫ point a)) (j ≫ point b) = 𝟙 D := by
    rw [ha, hb]
    apply product_hom_ext
    · apply product_hom_ext <;> simp [p, doubleTorus_base, doubleTorus_first]
    · simp [doubleTorus_last]
  have h₁ : productLift (productLift p (j ≫ point b)) (j ≫ point a⁻¹) = s ≫ i := by
    rw [hi, ← Category.assoc j (point a), ha, hb]
    apply product_hom_ext
    · apply product_hom_ext <;>
        simp [s, i, p, doubleTorus_base, doubleTorus_last, productSwapLast, Category.assoc]
    · simp [s, i, doubleTorus_first, productSwapLast, Category.assoc]
  let H := reducedDoubleTorusPairGraphSwapHomotopy j p a b
  obtain ⟨H₀, H₁⟩ := reducedDoubleTorusPairGraph_swapHomotopy_endpoints j p a b
  have hH₀ : γ (σ(0)) ≫ H = torusDoubleReduction k X := by
    rw [H₀, reducedDoubleTorusPairGraph]
    change γ (productLift (productLift p (j ≫ point a)) (j ≫ point b)) ≫ _ = _
    rw [h₀, CategoryTheory.Functor.map_id]
    exact Category.id_comp _
  have hH₁ : γ (σ(1)) ≫ H = γ (s ≫ i) ≫ torusDoubleReduction k X := by
    rw [H₁, reducedDoubleTorusPairGraph]
    change γ (productLift (productLift p (j ≫ point b)) (j ≫ point a⁻¹)) ≫ _ = _
    rw [h₁]
  have hn (r : k) : γ (σ(r)) ≫ γ (affineLineCylinder.map s) ≫ H =
      γ s ≫ γ (σ(r)) ≫ H := by
    rw [← Category.assoc, ← Functor.map_comp, nativeAffineSection_naturality,
      Functor.map_comp, Category.assoc]
  change γ (σ(0)) ≫ (γ (affineLineCylinder.map s) ≫ H) = _ ∧
    γ (σ(1)) ≫ (γ (affineLineCylinder.map s) ≫ H) = _
  constructor
  · rw [hn, hH₀]
  · rw [hn, hH₁, ← Category.assoc, ← Functor.map_comp, ← Category.assoc, hs, Category.id_comp]
    rfl

/-- The native swap is homotopic to outer inversion over every smooth base. -/
theorem exists_torusDoubleSwap_homotopy :
    ∃ H : Cor.mk (affineLineCylinder.obj D) ⟶ Cor.mk D,
      γ (σ(0)) ≫ H = torusDoubleSwap k X ≫ torusDoubleReduction k X ∧
      γ (σ(1)) ≫ H = torusDoubleInversion k X ≫ torusDoubleReduction k X :=
  ⟨torusDoubleSwapHomotopy k X, torusDoubleSwapHomotopy_endpoints k X⟩

set_option maxHeartbeats 1000000 in
-- The two product-face squares preserve the actual chart and the retained source map.
/-- The chosen native swap homotopy commutes with a Cartesian polynomial face of the base. -/
theorem torusDoubleSwapHomotopy_graph_precomp_of_cartesian_face
    {X' : Cor k} (f : X'.toSmoothSite ⟶ X₀)
    (q : (X₀).left ⟶ Spec (.of (Polynomial k))) [Flat q] (d : k)
    (H : IsPullback f.left X'.toSmoothSite.hom q (AffineLineFiber.point d)) :
    γ (affineLineCylinder.map (torusDoubleBaseMap k f)) ≫ torusDoubleSwapHomotopy k X =
      torusDoubleSwapHomotopy k X' ≫ γ (torusDoubleBaseMap k f) := by
  let : IsAffine (Tₖ).left := torusBinaryProduct_isAffine (k := k)
  let : IsIntegral (Tₖ).left := torusBinaryProduct_isIntegral (k := k)
  let R := Γ((Tₖ).left, ⊤)
  let : Algebra k R := sectionsAlgebra Tₖ
  let : Algebra.Smooth k R := sections_smooth Tₖ
  let : IsDomain R := IsIntegral.component_integral (⊤ : (Tₖ).left.Opens)
  let : IsNoetherianRing R := sections_isNoetherianRing Tₖ
  let : IsIntegrallyClosed R := sections_isIntegrallyClosed Tₖ
  let e : affineSite k R ≅ Tₖ := affineIso Tₖ
  let g := torusDoubleBaseMap k f
  let j := doubleTorus_pair k X₀ ≫ e.inv
  let j' := doubleTorus_pair k X'.toSmoothSite ≫ e.inv
  let p := doubleTorus_base k X₀
  let p' := doubleTorus_base k X'.toSmoothSite
  let : Flat (doubleTorus_pair k X₀).left := doubleTorus_pair_flat k X₀
  let : Flat (doubleTorus_pair k X'.toSmoothSite).left :=
    doubleTorus_pair_flat k X'.toSmoothSite
  let : IsIso e.inv.left :=
    inferInstanceAs (IsIso ((SmoothSite.forgetScheme Sₖ).mapIso e).inv)
  let : Flat j.left :=
    inferInstanceAs (Flat ((doubleTorus_pair k X₀).left ≫ e.inv.left))
  let : Flat j'.left :=
    inferInstanceAs (Flat ((doubleTorus_pair k X'.toSmoothSite).left ≫ e.inv.left))
  let a : Rˣ := affineUnitOfPoint (e.hom ≫ productFst Gₖ Gₖ)
  let b : Rˣ := affineUnitOfPoint (e.hom ≫ productSnd Gₖ Gₖ)
  have hj₀ : g ≫ doubleTorus_pair k X₀ = doubleTorus_pair k X'.toSmoothSite := by
    apply product_hom_ext <;> simp [g, torusDoubleBaseMap, doubleTorus_pair,
      doubleTorus_first, doubleTorus_last, Category.assoc]
  have hj : g ≫ j = j' := by
    change g ≫ doubleTorus_pair k X₀ ≫ e.inv = doubleTorus_pair k X'.toSmoothSite ≫ e.inv
    rw [← Category.assoc, hj₀]
  have hp : g ≫ p = p' ≫ f := by
    simp [g, torusDoubleBaseMap, p, p', doubleTorus_base, Category.assoc]
  let q₁ := pullback.fst (X₀).hom (Gₖ).hom ≫ q
  let q₂ := pullback.fst (XG).hom (Gₖ).hom ≫ q₁
  let : Flat q₂ := inferInstanceAs
    (Flat (pullback.fst (XG).hom (Gₖ).hom ≫ pullback.fst (X₀).hom (Gₖ).hom ≫ q))
  have H₁ := productMap_cartesian_polynomial_face f Gₖ q d H
  have H₂ := productMap_cartesian_polynomial_face (SmoothSite.productMap f (𝟙 Gₖ)) Gₖ q₁ d H₁
  have hpair := reducedDoubleTorusPairGraph_swapHomotopy_graph_precomp j p
    g f j' p' hj hp q₂ d H₂ a b
  let s := productSwapLast X₀ Gₖ Gₖ
  let s' := productSwapLast X'.toSmoothSite Gₖ Gₖ
  have hs : g ≫ s = s' ≫ g :=
    productSwapLast_naturality X'.toSmoothSite Gₖ Gₖ f (𝟙 Gₖ) (𝟙 Gₖ)
  change γ (affineLineCylinder.map g) ≫ γ (affineLineCylinder.map s) ≫
      reducedDoubleTorusPairGraphSwapHomotopy j p a b =
    (γ (affineLineCylinder.map s') ≫ reducedDoubleTorusPairGraphSwapHomotopy j' p' a b) ≫ γ g
  rw [← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, hs,
    Functor.map_comp, Functor.map_comp, Category.assoc, hpair, ← Category.assoc]

end AlgebraicGeometry.PresheafWithTransfers
