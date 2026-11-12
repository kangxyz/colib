/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.DoubleTorus
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.RetainedPencil
import Mathlib.Tactic.Abel

/-!
# The double-torus quadratic homotopy with an arbitrary retained base

The original base map is retained on each full quadratic support. The
paired endpoint graphs give additivity in each torus coordinate. The
diagonal endpoint graphs give diagonal additivity. Their signed combination
gives the interchange with inverse after the two unit-axis reductions.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory NativeTorusPolynomial
open AlgebraicGeometry.Scheme SmoothSite SmoothSite.Contraction AffineLineFiber

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k R : Type u} [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]
  {U' X : SmoothSite (Spec (CommRingCat.of k))}
  (j : U' ⟶ affineSite k R) (p : U' ⟶ X)

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Gₖ" => multiplicativeGroupObject Sₖ
local notation "Aₖ" => additiveGroupObject Sₖ
local notation "U" => affineSite k R
local notation "XG" => SmoothSite.product X Gₖ
local notation "XGG" => SmoothSite.product XG Gₖ
set_option quotPrecheck false in
local notation "V" => affineLineCylinder.obj U'
local notation "γ" => CategoryTheory.Functor.map (Cor.graphFunctor k)
local notation "red" => torusDoubleReduction k (Cor.mk X)
local notation "σ(" a ")" => nativeAffineSection (CommRingCat.of k) U' a
set_option quotPrecheck false in
local notation "pr" => (SmoothSite.Contraction.projection Aₖ).app U'
set_option quotPrecheck false in
local notation "point(" a ")" =>
  SmoothSite.homMk (X := U) (Y := Gₖ)
    (nativeAffineTorusPoint (U).hom a).left (affineUnitPoint_over (U).hom a)
local notation "pair(" a "," b ")" => productLift (productLift p (j ≫ point(a))) (j ≫ point(b))

/-- The actual graph of the two pulled-back units, retaining the original base map. -/
def reducedDoubleTorusPairGraph (a b : Rˣ) : Cor.mk U' ⟶ Cor.mk XGG :=
  γ (pair(a,b)) ≫ red

local notation "B(" a "," b ")" => reducedDoubleTorusPairGraph j p a b

private theorem point_one : point((1 : Rˣ)) = toBase U ≫ torusOne Sₖ := by
  apply MorphismProperty.Over.Hom.ext
  exact affineUnitPoint_one (U).hom

private theorem pairGraph_one_first (a : Rˣ) : B(1,a) = 0 := by
  unfold reducedDoubleTorusPairGraph
  rw [point_one (k := k) (R := R), comp_toBase_assoc]
  exact graph_doubleUnit_first_comp_reduction k p (j ≫ point(a))

private theorem pairGraph_one_last (a : Rˣ) : B(a,1) = 0 := by
  unfold reducedDoubleTorusPairGraph
  rw [point_one (k := k) (R := R), comp_toBase_assoc]
  exact graph_doubleUnit_last_comp_reduction k p (j ≫ point(a))

private theorem pair_comp_swap (a b : Rˣ) :
    pair(a,b) ≫ productSwapLast X Gₖ Gₖ = pair(b,a) := by
  apply product_hom_ext
  · apply product_hom_ext <;> simp [productSwapLast, Category.assoc]
  · simp [productSwapLast]

local notation "diagonal" => productLift (𝟙 XG) (productSnd X Gₖ)

private theorem pair_comp_diagonal (a : Rˣ) :
    productLift p (j ≫ point(a)) ≫ diagonal = pair(a,a) := by
  apply product_hom_ext <;> simp

private abbrev sectionGraph (T : SmoothSite (Spec (CommRingCat.of k))) (r : k) :
    Cor.mk T ⟶ Cor.mk (affineLineCylinder.obj T) :=
  γ (nativeAffineSection (.of k) T r)

private abbrev projectionGraph (T : SmoothSite (Spec (CommRingCat.of k))) :
    Cor.mk (affineLineCylinder.obj T) ⟶ Cor.mk T :=
  γ ((SmoothSite.Contraction.projection Aₖ).app T)

local notation "keep(" a ")" => productLift (pr ≫ p) (pr ≫ j ≫ point(a))

private theorem section_keep (a : k) (b : Rˣ) :
    σ(a) ≫ keep(b) = productLift p (j ≫ point(b)) := by
  apply product_hom_ext
  · simp only [Category.assoc, productLift_fst, nativeAffineSection_projection_assoc]
  · simp only [Category.assoc, productLift_snd, nativeAffineSection_projection_assoc]

variable [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Flat j.left]

private def rightPencil (a b c : Rˣ) : Cor.mk V ⟶ Cor.mk XGG :=
  Cor.retainedUnitProductCylinderCycle j (keep(c)) a b ≫ torusDoubleSwap k (Cor.mk X) ≫ red

private def leftPencil (a b c : Rˣ) : Cor.mk V ⟶ Cor.mk XGG :=
  Cor.retainedUnitProductCylinderCycle j (keep(c)) a b ≫ red

private def diagonalPencil (a b : Rˣ) : Cor.mk V ⟶ Cor.mk XGG :=
  Cor.retainedUnitProductCylinderCycle j (pr ≫ p) a b ≫ γ diagonal ≫ red

private theorem rightPencil_zero (a b c : Rˣ) :
    γ (σ(0)) ≫ rightPencil j p a b c = B(a * b,c) := by
  rw [rightPencil, ← Category.assoc, Cor.nativeSection_zero_comp_retainedUnitProductCylinderCycle,
    section_keep]
  simp only [Preadditive.add_comp, ← Category.assoc, torusDoubleSwap, ← Functor.map_comp,
    pair_comp_swap]
  change B(a * b,c) + B(1,c) = _
  rw [pairGraph_one_first, add_zero]

private theorem rightPencil_one (a b c : Rˣ) :
    γ (σ(1)) ≫ rightPencil j p a b c = B(a,c) + B(b,c) := by
  rw [rightPencil, ← Category.assoc, Cor.nativeSection_one_comp_retainedUnitProductCylinderCycle,
    section_keep]
  simp only [Preadditive.add_comp, ← Category.assoc, torusDoubleSwap, ← Functor.map_comp,
    pair_comp_swap, reducedDoubleTorusPairGraph]

private theorem leftPencil_zero (a b c : Rˣ) :
    γ (σ(0)) ≫ leftPencil j p a b c = B(c,a * b) := by
  rw [leftPencil, ← Category.assoc, Cor.nativeSection_zero_comp_retainedUnitProductCylinderCycle,
    section_keep, Preadditive.add_comp]
  change B(c,a * b) + B(c,1) = _
  rw [pairGraph_one_last, add_zero]

private theorem leftPencil_one (a b c : Rˣ) :
    γ (σ(1)) ≫ leftPencil j p a b c = B(c,a) + B(c,b) := by
  rw [leftPencil, ← Category.assoc, Cor.nativeSection_one_comp_retainedUnitProductCylinderCycle,
    section_keep]
  simp only [Preadditive.add_comp, reducedDoubleTorusPairGraph]

private theorem diagonalPencil_zero (a b : Rˣ) :
    γ (σ(0)) ≫ diagonalPencil j p a b = B(a * b,a * b) := by
  rw [diagonalPencil, ← Category.assoc,
    Cor.nativeSection_zero_comp_retainedUnitProductCylinderCycle,
    nativeAffineSection_projection_assoc]
  simp only [Preadditive.add_comp, ← Category.assoc, ← Functor.map_comp, pair_comp_diagonal]
  change B(a * b,a * b) + B(1,1) = _
  rw [pairGraph_one_first, add_zero]

private theorem diagonalPencil_one (a b : Rˣ) :
    γ (σ(1)) ≫ diagonalPencil j p a b = B(a,a) + B(b,b) := by
  rw [diagonalPencil, ← Category.assoc, Cor.nativeSection_one_comp_retainedUnitProductCylinderCycle,
    nativeAffineSection_projection_assoc]
  simp only [Preadditive.add_comp, ← Category.assoc, ← Functor.map_comp, pair_comp_diagonal,
    reducedDoubleTorusPairGraph]

private def swapBoundary (a b : Rˣ) : Cor.mk V ⟶ Cor.mk XGG :=
  diagonalPencil j p a b - rightPencil j p a b (a * b) -
    leftPencil j p a b a - leftPencil j p a b b + leftPencil j p a a⁻¹ b

private theorem swapBoundary_sub (a b : Rˣ) :
    γ (σ(0)) ≫ swapBoundary j p a b - γ (σ(1)) ≫ swapBoundary j p a b =
      B(a,b) - B(b,a⁻¹) := by
  simp only [swapBoundary, Preadditive.comp_sub, Preadditive.comp_add,
    diagonalPencil_zero, diagonalPencil_one, rightPencil_zero, rightPencil_one,
    leftPencil_zero, leftPencil_one, mul_inv_cancel, pairGraph_one_last]
  change (B(a * b,a * b) - B(a * b,a * b) - B(a,a * b) - B(b,a * b) + 0) -
    ((B(a,a) + B(b,b)) - (B(a,a * b) + B(b,a * b)) - (B(a,a) + B(a,b)) -
      (B(b,a) + B(b,b)) + (B(b,a) + B(b,a⁻¹))) = B(a,b) - B(b,a⁻¹)
  abel

/-- The actual signed pencil homotopy, corrected by its constant endpoint. -/
@[no_expose]
def reducedDoubleTorusPairGraph_swapHomotopy (a b : Rˣ) : Cor.mk V ⟶ Cor.mk XGG :=
  let H := swapBoundary j p a b
  H + projectionGraph U' ≫ (B(b,a⁻¹) - sectionGraph U' 1 ≫ H)

/-- The retained base is unchanged at both actual endpoints of the signed pencil. -/
theorem reducedDoubleTorusPairGraph_swapHomotopy_endpoints (a b : Rˣ) :
    γ (σ(0)) ≫ reducedDoubleTorusPairGraph_swapHomotopy j p a b = B(a,b) ∧
      γ (σ(1)) ≫ reducedDoubleTorusPairGraph_swapHomotopy j p a b = B(b,a⁻¹) := by
  let H := swapBoundary j p a b
  let c := B(b,a⁻¹) - sectionGraph U' 1 ≫ H
  have hc (r : k) : sectionGraph U' r ≫ projectionGraph U' ≫ c = c := by
    change γ (σ(r)) ≫ γ pr ≫ c = c
    rw [← Category.assoc, ← Functor.map_comp, nativeAffineSection_projection,
      CategoryTheory.Functor.map_id]
    exact Category.id_comp c
  have hb : sectionGraph U' 0 ≫ H - sectionGraph U' 1 ≫ H = B(a,b) - B(b,a⁻¹) :=
    swapBoundary_sub j p a b
  change sectionGraph U' 0 ≫ (H + projectionGraph U' ≫ c) = B(a,b) ∧
    sectionGraph U' 1 ≫ (H + projectionGraph U' ≫ c) = B(b,a⁻¹)
  constructor
  · rw [Preadditive.comp_add, hc]
    change sectionGraph U' 0 ≫ H + (B(b,a⁻¹) - sectionGraph U' 1 ≫ H) = B(a,b)
    calc
      _ = (sectionGraph U' 0 ≫ H - sectionGraph U' 1 ≫ H) + B(b,a⁻¹) := by abel
      _ = _ := by rw [hb, sub_add_cancel]
  · rw [Preadditive.comp_add, hc]
    change sectionGraph U' 1 ≫ H + (B(b,a⁻¹) - sectionGraph U' 1 ≫ H) = B(b,a⁻¹)
    abel

/-- The two reduced graph correspondences are joined by a finite correspondence
on the original affine-line cylinder. -/
theorem exists_reducedDoubleTorusPairGraph_swap_homotopy (a b : Rˣ) :
    ∃ H : Cor.mk V ⟶ Cor.mk XGG,
      γ (σ(0)) ≫ H = B(a,b) ∧ γ (σ(1)) ≫ H = B(b,a⁻¹) :=
  ⟨reducedDoubleTorusPairGraph_swapHomotopy j p a b,
    reducedDoubleTorusPairGraph_swapHomotopy_endpoints j p a b⟩

set_option maxHeartbeats 1200000 in
-- Each signed pencil retains a different actual target map across the same Cartesian face.
omit [IsIntegrallyClosed R] in
/-- The chosen retained swap homotopy commutes with a Cartesian polynomial face. -/
theorem reducedDoubleTorusPairGraph_swapHomotopy_graph_precomp
    {U'' X' : SmoothSite (Spec (CommRingCat.of k))}
    (g : U'' ⟶ U') (f : X' ⟶ X) (j' : U'' ⟶ U) [Flat j'.left] (p' : U'' ⟶ X')
    (hj : g ≫ j = j') (hp : g ≫ p = p' ≫ f)
    (t : U'.left ⟶ Spec (.of (Polynomial k))) [Flat t] (d : k)
    (H : IsPullback g.left U''.hom t (AffineLineFiber.point d)) (a b : Rˣ) :
    γ (affineLineCylinder.map g) ≫ reducedDoubleTorusPairGraph_swapHomotopy j p a b =
      reducedDoubleTorusPairGraph_swapHomotopy j' p' a b ≫ γ (torusDoubleBaseMap k f) := by
  let c : Cor.mk (affineLineCylinder.obj U'') ⟶ Cor.mk V := γ (affineLineCylinder.map g)
  let g₀ : Cor.mk U'' ⟶ Cor.mk U' := γ g
  let m := torusDoubleBaseMap k f
  let n : Cor.mk (SmoothSite.product (SmoothSite.product X' Gₖ) Gₖ) ⟶ Cor.mk XGG := γ m
  let pr' := (SmoothSite.Contraction.projection Aₖ).app U''
  let keep' (w : Rˣ) := productLift (pr' ≫ p') (pr' ≫ j' ≫ point(w))
  let diag' := productLift (𝟙 (SmoothSite.product X' Gₖ)) (productSnd X' Gₖ)
  have hpr : affineLineCylinder.map g ≫ pr = pr' ≫ g :=
    (SmoothSite.Contraction.projection Aₖ).naturality g
  have hbase : affineLineCylinder.map g ≫ pr ≫ p = (pr' ≫ p') ≫ f := by
    calc
      _ = (affineLineCylinder.map g ≫ pr) ≫ p := (Category.assoc _ _ _).symm
      _ = (pr' ≫ g) ≫ p := congrArg (· ≫ p) hpr
      _ = pr' ≫ (g ≫ p) := Category.assoc _ _ _
      _ = pr' ≫ (p' ≫ f) := congrArg (pr' ≫ ·) hp
      _ = _ := (Category.assoc _ _ _).symm
  have hkeep (w : Rˣ) : affineLineCylinder.map g ≫ keep(w) =
      keep' w ≫ SmoothSite.productMap f (𝟙 Gₖ) := by
    apply product_hom_ext
    · simpa only [Category.assoc, productLift_fst, productLift_fst_assoc, productMap_fst, keep']
        using hbase
    · simp only [Category.assoc, productLift_snd, productMap_snd, Category.comp_id, keep']
      rw [← Category.assoc, hpr, Category.assoc, ← Category.assoc g j, hj]
  have hret (u v w : Rˣ) : c ≫ Cor.retainedUnitProductCylinderCycle j (keep(w)) u v =
      Cor.retainedUnitProductCylinderCycle j' (keep' w) u v ≫ n :=
    Cor.retainedUnitProductCylinderCycle_graph_precomp g
      (SmoothSite.productMap f (𝟙 Gₖ)) j j' hj _ _ (hkeep w) t d H u v
  have hred : n ≫ red = torusDoubleReduction k (Cor.mk X') ≫ n :=
    torusDoubleReduction_baseMap k f
  have hswap : n ≫ torusDoubleSwap k (Cor.mk X) = torusDoubleSwap k (Cor.mk X') ≫ n :=
    torusDoubleSwap_baseMap k f
  have hswap_red : n ≫ torusDoubleSwap k (Cor.mk X) ≫ red =
      torusDoubleSwap k (Cor.mk X') ≫ torusDoubleReduction k (Cor.mk X') ≫ n := by
    rw [← Category.assoc, hswap, Category.assoc, hred]
  have hright (u v w : Rˣ) : c ≫ rightPencil j p u v w = rightPencil j' p' u v w ≫ n := by
    simp only [rightPencil]
    rw [← Category.assoc, hret, Category.assoc, hswap_red]
    simp only [Category.assoc, keep', pr']
  have hleft (u v w : Rˣ) : c ≫ leftPencil j p u v w = leftPencil j' p' u v w ≫ n := by
    simp only [leftPencil]
    rw [← Category.assoc, hret, Category.assoc, hred]
    simp only [Category.assoc, keep', pr']
  have hdiag_map : SmoothSite.productMap f (𝟙 Gₖ) ≫ diagonal = diag' ≫ m := by
    apply product_hom_ext <;> simp [diag', m, torusDoubleBaseMap, Category.assoc]
  have hdiag_graph : γ (SmoothSite.productMap f (𝟙 Gₖ)) ≫ γ diagonal = γ diag' ≫ n := by
    rw [← Functor.map_comp, ← Functor.map_comp, hdiag_map]
  have hdiag_ret (u v : Rˣ) : c ≫ Cor.retainedUnitProductCylinderCycle j (pr ≫ p) u v =
      Cor.retainedUnitProductCylinderCycle j' (pr' ≫ p') u v ≫
        γ (SmoothSite.productMap f (𝟙 Gₖ)) :=
    Cor.retainedUnitProductCylinderCycle_graph_precomp g f j j' hj _ _ hbase t d H u v
  have hdiag (u v : Rˣ) : c ≫ diagonalPencil j p u v = diagonalPencil j' p' u v ≫ n := by
    simp only [diagonalPencil]
    rw [← Category.assoc, hdiag_ret, Category.assoc, ← Category.assoc
      (γ (SmoothSite.productMap f (𝟙 Gₖ))), hdiag_graph, Category.assoc, hred]
    simp only [Category.assoc, diag', pr']
  have hbound : c ≫ swapBoundary j p a b = swapBoundary j' p' a b ≫ n := by
    simp only [swapBoundary, Preadditive.comp_sub, Preadditive.comp_add, hright, hleft, hdiag,
      Preadditive.add_comp, Preadditive.sub_comp]
  have hpair (u v : Rˣ) : g₀ ≫ B(u,v) = reducedDoubleTorusPairGraph j' p' u v ≫ n := by
    have hj' (w : Rˣ) : g ≫ j ≫ point(w) = j' ≫ point(w) := by rw [← Category.assoc, hj]
    have he : g ≫ pair(u,v) =
        productLift (productLift p' (j' ≫ point(u))) (j' ≫ point(v)) ≫ m := by
      apply product_hom_ext
      · apply product_hom_ext <;> simp [m, torusDoubleBaseMap, Category.assoc, hp, hj']
      · simp [m, torusDoubleBaseMap, Category.assoc, hj']
    change γ g ≫ B(u,v) = reducedDoubleTorusPairGraph j' p' u v ≫ n
    unfold reducedDoubleTorusPairGraph
    rw [← Category.assoc, ← Functor.map_comp, he, Functor.map_comp, Category.assoc, hred,
      ← Category.assoc]
  have hsection : g₀ ≫ sectionGraph U' 1 = sectionGraph U'' 1 ≫ c := by
    change γ g ≫ γ (σ(1)) =
      γ (nativeAffineSection (.of k) U'' 1) ≫ γ (affineLineCylinder.map g)
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact (Cor.graphFunctor k).congr_map (nativeAffineSection_naturality (.of k) g 1).symm
  have hpr_graph : c ≫ projectionGraph U' = projectionGraph U'' ≫ g₀ := by
    change γ (affineLineCylinder.map g) ≫ γ pr = γ pr' ≫ γ g
    rw [← Functor.map_comp, ← Functor.map_comp, hpr]
  let C := B(b,a⁻¹) - sectionGraph U' 1 ≫ swapBoundary j p a b
  let C' := reducedDoubleTorusPairGraph j' p' b a⁻¹ - sectionGraph U'' 1 ≫ swapBoundary j' p' a b
  have hC : g₀ ≫ C = C' ≫ n := by
    change g₀ ≫ (B(b,a⁻¹) - sectionGraph U' 1 ≫ swapBoundary j p a b) =
      (reducedDoubleTorusPairGraph j' p' b a⁻¹ - sectionGraph U'' 1 ≫ swapBoundary j' p' a b) ≫ n
    rw [Preadditive.comp_sub, hpair, ← Category.assoc, hsection, Category.assoc, hbound,
      Preadditive.sub_comp, Category.assoc]
  change c ≫ (swapBoundary j p a b + projectionGraph U' ≫ C) =
    (swapBoundary j' p' a b + projectionGraph U'' ≫ C') ≫ n
  rw [Preadditive.comp_add, hbound, ← Category.assoc, hpr_graph, Category.assoc, hC,
    Preadditive.add_comp, Category.assoc]

end AlgebraicGeometry.PresheafWithTransfers
