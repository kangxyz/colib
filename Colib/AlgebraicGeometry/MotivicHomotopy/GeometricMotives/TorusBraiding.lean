/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.GeometricMotives.Additivity
public import Colib.AlgebraicGeometry.MotivicHomotopy.GeometricMotives.AffineContraction
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.DoubleTorus
import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.RetainedSwap

/-! # The swap on the doubly reduced torus motive

The retained quadratic family shows that outer inversion acts by a minus sign
after double reduction. The native double-torus homotopy identifies outer
inversion with the swap after this same projector.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NativeTorusPolynomial
open AlgebraicGeometry.Scheme SmoothSite SmoothSite.Contraction
open AlgebraicGeometry.Scheme.SmoothSite.AffineSectionCoordinates

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "G" => multiplicativeGroupObject S
local notation "γ" => CategoryTheory.Functor.map (Cor.graphFunctor k)
local notation "A(" Y ")" => affineLineCylinder.obj Y
local notation "σ(" Y "," t ")" => nativeAffineSection (CommRingCat.of k) Y t

private theorem torusUnitProjector_comp_doubleReduction (X : Cor k) :
    torusUnitProjector k ((Cor.parameterProduct G).obj X) ≫ torusDoubleReduction k X = 0 := by
  let P := Cor.parameterProduct G
  let D := P.obj (P.obj X)
  let i : D ⟶ D := P.map (torusUnitProjector k X)
  let o : D ⟶ D := torusUnitProjector k (P.obj X)
  have h : o ≫ i = i ≫ o := (torusUnitProjector_naturality k (torusUnitProjector k X)).symm
  have hi : o ≫ (𝟙 _ - i) = (𝟙 _ - i) ≫ o := by
    simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id, Category.id_comp, h]
  have ho : o ≫ (𝟙 _ - o) = 0 := by
    change torusUnitProjector k ((P).obj X) ≫ (𝟙 _ - torusUnitProjector k ((P).obj X)) = 0
    rw [Preadditive.comp_sub, Category.comp_id, torusUnitProjector_idempotent, sub_self]
  change o ≫ ((𝟙 _ - i) ≫ (𝟙 _ - o)) = 0
  rw [← Category.assoc, hi, Category.assoc, ho, comp_zero]

set_option maxHeartbeats 800000 in
-- The affine chart, flat pullback, and retained endpoint graphs have dependent source types.
private theorem outerInversionPencil_endpoints (U : SmoothSite S) :
    ∃ H : Cor.mk (A(SmoothSite.product U G)) ⟶ Cor.mk (SmoothSite.product U G),
      γ (σ(SmoothSite.product U G,0)) ≫ H =
        torusUnitProjector k (Cor.mk U) + torusUnitProjector k (Cor.mk U) ∧
      γ (σ(SmoothSite.product U G,1)) ≫ H =
        𝟙 _ + (Cor.parameterProductMap (torusInversion S)).app (Cor.mk U) := by
  let D := SmoothSite.product U G
  let eG := torusFieldChart (k := k)
  let : IsAffine (G).left := IsAffine.of_isIso eG.inv
  let : IsIntegral (G).left := IsIntegral.of_isIso eG.hom
  let R := Γ((G).left, ⊤)
  let : Algebra k R := sectionsAlgebra G
  let : Algebra.Smooth k R := sections_smooth G
  let : IsNoetherianRing R := sections_isNoetherianRing G
  let : IsDomain R := IsIntegral.component_integral (⊤ : (G).left.Opens)
  let : IsIntegrallyClosed R := sections_isIntegrallyClosed G
  let V := affineSite k R
  let e : V ≅ G := affineIso (k := k) G
  let a : Rˣ := affineUnitOfPoint (k := k) (R := R) e.hom
  let p (v : Rˣ) : V ⟶ G :=
    SmoothSite.homMk (nativeAffineTorusPoint V.hom v).left (affineUnitPoint_over V.hom v)
  have ha : p a = e.hom := affineUnitOfPoint_recover (k := k) (R := R) e.hom
  have hai : p (a⁻¹) = e.hom ≫ torusInversion S := by
    rw [← ha]
    exact (affineUnitPoint_comp_torusInversion (k := k) (R := R) a).symm
  have hone : p 1 = toBase V ≫ torusOne S := by
    apply MorphismProperty.Over.Hom.ext
    exact affineUnitPoint_one V.hom
  let j : D ⟶ V := productSnd U G ≫ e.inv
  let : Flat (productSnd U G).left := inferInstanceAs (Flat (pullback.snd U.hom (G).hom))
  let : IsIso e.inv.left := inferInstanceAs (IsIso ((SmoothSite.forgetScheme S).mapIso e).inv)
  let : Flat j.left := inferInstanceAs (Flat ((productSnd U G).left ≫ e.inv.left))
  let r : A(D) ⟶ U := (projection (additiveGroupObject S)).app D ≫ productFst U G
  have hr (t : k) : σ(D,t) ≫ r = productFst U G := by
    change σ(D,t) ≫ (projection (additiveGroupObject S)).app D ≫ productFst U G = _
    rw [nativeAffineSection_projection_assoc]
  have hj : j ≫ p a = productSnd U G := by
    rw [ha]
    change (productSnd U G ≫ e.inv) ≫ e.hom = _
    rw [Category.assoc, e.inv_hom_id, Category.comp_id]
  have hji : j ≫ p (a⁻¹) = productSnd U G ≫ torusInversion S := by
    rw [hai, ← Category.assoc, ← ha, hj]
  have hj1 : j ≫ p 1 = toBase D ≫ torusOne S := by
    rw [hone, comp_toBase_assoc]
  let P : Cor.mk D ⟶ Cor.mk D := torusUnitProjector k (Cor.mk U)
  let I : Cor.mk D ⟶ Cor.mk D := γ (SmoothSite.productMap (𝟙 U) (torusInversion S))
  have hP : γ (productLift (productFst U G) (toBase D ≫ torusOne S)) = P := by
    rw [show P = γ (productFst U G ≫ unitSection.app U) from torusUnitProjector_eq_graph k _]
    apply (Cor.graphFunctor k).congr_map
    apply product_hom_ext
    · simp [unitSection, Category.assoc]
    · simp [unitSection, Category.assoc]
      rfl
  have hI : γ (productLift (productFst U G) (productSnd U G ≫ torusInversion S)) = I :=
    (Cor.graphFunctor k).congr_map (by simp only [SmoothSite.productMap, Category.comp_id])
  have hid : γ (productLift (productFst U G) (productSnd U G)) = 𝟙 (Cor.mk D) := by
    have h : productLift (productFst U G) (productSnd U G) = 𝟙 D := by
      apply product_hom_ext
      · exact (productLift_fst (productFst U G) (productSnd U G)).trans
          (Category.id_comp (productFst U G)).symm
      · exact (productLift_snd (productFst U G) (productSnd U G)).trans
          (Category.id_comp (productSnd U G)).symm
    exact ((Cor.graphFunctor k).congr_map h).trans ((Cor.graphFunctor k).map_id D)
  let H : Cor.mk (A(D)) ⟶ Cor.mk D := Cor.retainedUnitProductCylinderCycle j r a (a⁻¹)
  have h₀ : γ (σ(D,0)) ≫ H = P + P := by
    dsimp only [H]
    rw [Cor.nativeSection_zero_comp_retainedUnitProductCylinderCycle]
    rw [mul_inv_cancel, hr]
    change γ (productLift (productFst U G) (j ≫ p 1)) +
      γ (productLift (productFst U G) (j ≫ p 1)) = P + P
    rw [hj1, hP]
  have h₁ : γ (σ(D,1)) ≫ H = 𝟙 _ + I := by
    dsimp only [H]
    rw [Cor.nativeSection_one_comp_retainedUnitProductCylinderCycle]
    rw [hr]
    change γ (productLift (productFst U G) (j ≫ p a)) +
      γ (productLift (productFst U G) (j ≫ p (a⁻¹))) = 𝟙 (Cor.mk D) + I
    rw [hj, hji, hid, hI]
  exact ⟨H, h₀, h₁⟩

variable [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "M" => effectiveSmoothMotive k
local notation "F" => effectiveMotive k

private theorem map_nativeAffineSection_eq (Y : SmoothSite S) :
    (F).map (γ (σ(Y,0))) = (F).map (γ (σ(Y,1))) := by
  let p := (projection (additiveGroupObject S)).app Y
  let : IsIso ((M).map p) := isIso_effectiveSmoothMotive_affineLineProjection k Y
  have h (t : k) : (M).map (σ(Y,t)) ≫ (M).map p = 𝟙 _ := by
    rw [← (M).map_comp, nativeAffineSection_projection, (M).map_id]
  exact (cancel_mono ((M).map p)).1 ((h 0).trans (h 1).symm)

private theorem map_torusDoubleInversion_comp_reduction (X : Cor k) :
    (F).map (torusDoubleInversion k X ≫ torusDoubleReduction k X) =
      -(F).map (torusDoubleReduction k X) := by
  let U := SmoothSite.product X.toSmoothSite G
  let D := SmoothSite.product U G
  let E : Cor.mk D ⟶ Cor.mk D := torusDoubleReduction k X
  let I : Cor.mk D ⟶ Cor.mk D := torusDoubleInversion k X
  let P : Cor.mk D ⟶ Cor.mk D := torusUnitProjector k (Cor.mk U)
  obtain ⟨H, h₀, h₁⟩ := outerInversionPencil_endpoints k U
  change γ (σ(D,0)) ≫ H = P + P at h₀
  change γ (σ(D,1)) ≫ H = 𝟙 (Cor.mk D) + I at h₁
  have h : (F).map (P + P) = (F).map (𝟙 _ + I) := by
    calc
      _ = (F).map (γ (σ(D,0)) ≫ H) := (F).congr_map h₀.symm
      _ = (F).map (γ (σ(D,1)) ≫ H) := by
        rw [(F).map_comp, (F).map_comp, map_nativeAffineSection_eq k D]
      _ = _ := (F).congr_map h₁
  have hPE : P ≫ E = 0 := torusUnitProjector_comp_doubleReduction k X
  have h' := congrArg (· ≫ (F).map E) h.symm
  rw [← (F).map_comp, ← (F).map_comp, Preadditive.add_comp, Preadditive.add_comp,
    Category.id_comp, hPE, add_zero, (F).map_zero, (F).map_add] at h'
  exact eq_neg_iff_add_eq_zero.mpr ((add_comm _ _).trans h')

/-- The actual double-torus swap acts by minus the identity on the double reduction. -/
theorem effectiveMotive_map_torusDoubleSwap_comp_reduction (X : Cor k) :
    (F).map (torusDoubleSwap k X ≫ torusDoubleReduction k X) =
      -(F).map (torusDoubleReduction k X) := by
  let D := SmoothSite.product (SmoothSite.product X.toSmoothSite G) G
  let H := torusDoubleSwapHomotopy k X
  obtain ⟨h₀, h₁⟩ := torusDoubleSwapHomotopy_endpoints k X
  calc
    _ = (F).map (γ (σ(D,0)) ≫ H) := (F).congr_map h₀.symm
    _ = (F).map (γ (σ(D,1)) ≫ H) := by
      rw [(F).map_comp, (F).map_comp, map_nativeAffineSection_eq k D]
    _ = (F).map (torusDoubleInversion k X ≫ torusDoubleReduction k X) := (F).congr_map h₁
    _ = _ := map_torusDoubleInversion_comp_reduction k X

end AlgebraicGeometry.MotivicHomotopy
