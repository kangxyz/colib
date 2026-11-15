/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.ReducedTorusObject
public import Colib.AlgebraicGeometry.MotivicHomotopy.GeometricMotives.TorusBraiding
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.Category
import Colib.AlgebraicGeometry.MotivicHomotopy.GeometricMotives.Additivity

/-!
# The sign on two Lefschetz factors

The two original unit-axis projectors cut out the double reduced torus.
The switch on that summand has sign minus one. Shifting both factors by
one adds the second minus sign from the cochain tensor.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open AlgebraicGeometry.Scheme SmoothSite.Contraction
open scoped MonoidalCategory

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "S" => Spec (CommRingCat.of k)
local notation "B" => SmoothSite.base S
local notation "G" => SmoothSite.multiplicativeGroupObject S
local notation "D" => SmoothSite.product (SmoothSite.product B G) G
local notation "V" => SmoothSite.product G G
local notation "M" => effectiveMotive k
set_option quotPrecheck false in
local notation "γ" => CategoryTheory.Functor.map (Cor.graphFunctor k)
local notation "p" => toBase G ≫ SmoothSite.torusOne S

attribute [local instance] BraidedCategory.ofCartesianMonoidalCategory

/-- The map forgetting the redundant base factor on a double torus. -/
private def doubleTorusComparison : D ⟶ V :=
  SmoothSite.productMap (SmoothSite.productSnd B G) (𝟙 G)

private instance : IsIso (doubleTorusComparison k) := by
  let e := torusBaseProduct (k := k)
  let i := SmoothSite.productMap e.inv (𝟙 G)
  refine ⟨⟨i, ?_, ?_⟩⟩
  · change SmoothSite.productMap e.hom (𝟙 G) ≫ SmoothSite.productMap e.inv (𝟙 G) = 𝟙 _
    rw [← SmoothSite.productMap_comp, e.hom_inv_id, Category.comp_id, SmoothSite.productMap_id]
  · change SmoothSite.productMap e.inv (𝟙 G) ≫ SmoothSite.productMap e.hom (𝟙 G) = 𝟙 _
    rw [← SmoothSite.productMap_comp, e.inv_hom_id, Category.comp_id, SmoothSite.productMap_id]

omit [PerfectField k] [HasDerivedCategory (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory (SheafWithTransfers.{u + 1} k)] [HasDerivedCategory AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})] in
private theorem doubleTorusComparison_swap :
    SmoothSite.productSwapLast B G G ≫ doubleTorusComparison k =
      doubleTorusComparison k ≫ (β_ G G).hom := by
  have h₁ : (β_ G G).hom ≫ SmoothSite.productFst G G = SmoothSite.productSnd G G :=
    CartesianMonoidalCategory.braiding_hom_fst G G
  have h₂ : (β_ G G).hom ≫ SmoothSite.productSnd G G = SmoothSite.productFst G G :=
    CartesianMonoidalCategory.braiding_hom_snd G G
  apply SmoothSite.product_hom_ext
  · simp [doubleTorusComparison, Category.assoc, h₁]
  · simp [doubleTorusComparison, Category.assoc, h₂]

omit [PerfectField k] [HasDerivedCategory (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory (SheafWithTransfers.{u + 1} k)] [HasDerivedCategory AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})] in
private theorem doubleTorusComparison_inner :
    (Cor.parameterProduct G).map (torusUnitProjector k (Cor.mk B)) ≫ γ (doubleTorusComparison k) =
      γ (doubleTorusComparison k) ≫ γ (SmoothSite.productMap p (𝟙 G)) := by
  let u : SmoothSite.product B G ⟶ SmoothSite.product B G := SmoothSite.productMap (𝟙 B) p
  let v := doubleTorusComparison k
  let t : G ⟶ G := p
  let F := Cor.graphFunctor k
  have hu : torusUnitProjector k (Cor.mk B) = F.map u :=
    torusUnitProjector_eq_productMap k (Cor.mk B)
  have hy : (Cor.parameterProduct G).map (F.map u) = F.map (SmoothSite.productMap u (𝟙 G)) :=
    Cor.parameterProduct_graph G u
  have h : SmoothSite.productMap u (𝟙 G) ≫ v = v ≫ SmoothSite.productMap t (𝟙 G) := by
    have hf : u ≫ SmoothSite.productSnd B G = SmoothSite.productSnd B G ≫ t :=
      SmoothSite.productMap_snd (𝟙 B) t
    change _ ≫ SmoothSite.productMap (SmoothSite.productSnd B G) (𝟙 G) =
      SmoothSite.productMap (SmoothSite.productSnd B G) (𝟙 G) ≫ _
    rw [← SmoothSite.productMap_comp, ← SmoothSite.productMap_comp, hf]
  calc
    _ = F.map (SmoothSite.productMap u (𝟙 G)) ≫ F.map v :=
      congrArg (· ≫ F.map v) ((congrArg (Cor.parameterProduct G).map hu).trans hy)
    _ = _ := ((F.map_comp _ _).symm.trans ((F.congr_map h).trans (F.map_comp _ _)))

omit [PerfectField k] [HasDerivedCategory (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory (SheafWithTransfers.{u + 1} k)] [HasDerivedCategory AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})] in
private theorem doubleTorusComparison_outer :
    torusUnitProjector k (Cor.mk (SmoothSite.product B G)) ≫ γ (doubleTorusComparison k) =
      γ (doubleTorusComparison k) ≫ γ (SmoothSite.productMap (𝟙 G) p) := by
  let u : D ⟶ D := SmoothSite.productMap (𝟙 (SmoothSite.product B G)) p
  let v := doubleTorusComparison k
  let F := Cor.graphFunctor k
  have hu : torusUnitProjector k (Cor.mk (SmoothSite.product B G)) = F.map u :=
    torusUnitProjector_eq_productMap k (Cor.mk (SmoothSite.product B G))
  have h : u ≫ v = v ≫ SmoothSite.productMap (𝟙 G) p := by
    change SmoothSite.productMap (𝟙 _) p ≫ SmoothSite.productMap (SmoothSite.productSnd B G) (𝟙 G) =
      SmoothSite.productMap (SmoothSite.productSnd B G) (𝟙 G) ≫ SmoothSite.productMap (𝟙 G) p
    rw [← SmoothSite.productMap_comp, ← SmoothSite.productMap_comp]
    simp only [Category.id_comp, Category.comp_id]
  calc
    _ = F.map u ≫ F.map v := congrArg (· ≫ F.map v) hu
    _ = _ := (F.map_comp _ _).symm.trans ((F.congr_map h).trans (F.map_comp _ _))

/-- The actual double reduced projector on the literal product of two tori. -/
def doubleTorusProjector : Cor.mk V ⟶ Cor.mk V :=
  (𝟙 _ - γ (SmoothSite.productMap p (𝟙 G))) ≫
    (𝟙 _ - γ (SmoothSite.productMap (𝟙 G) p))

omit [Field k] [PerfectField k] [HasDerivedCategory (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory (SheafWithTransfers.{u + 1} k)] [HasDerivedCategory AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})] in
private theorem comp_complement_projectors {C : Type*} [Category C] [Preadditive C]
    {U W : C} (f : U ⟶ W) (a b : U ⟶ U) (a' b' : W ⟶ W)
    (ha : a ≫ f = f ≫ a') (hb : b ≫ f = f ≫ b') :
    ((𝟙 U - a) ≫ (𝟙 U - b)) ≫ f = f ≫ ((𝟙 W - a') ≫ (𝟙 W - b')) := by
  have h₁ : (𝟙 U - a) ≫ f = f ≫ (𝟙 W - a') := by
    rw [Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp, Category.comp_id, ha]
  have h₂ : (𝟙 U - b) ≫ f = f ≫ (𝟙 W - b') := by
    rw [Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp, Category.comp_id, hb]
  rw [Category.assoc, h₂, reassoc_of% h₁]

omit [PerfectField k] [HasDerivedCategory (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory (SheafWithTransfers.{u + 1} k)] [HasDerivedCategory AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})] in
private theorem doubleTorusComparison_projector :
    torusDoubleReduction k (Cor.mk B) ≫ γ (doubleTorusComparison k) =
      γ (doubleTorusComparison k) ≫ doubleTorusProjector k := by
  let P := Cor.parameterProduct G
  let U := Cor.mk D
  let V₀ := Cor.mk V
  let f : U ⟶ V₀ := γ (doubleTorusComparison k)
  let a : U ⟶ U := P.map (torusUnitProjector k (Cor.mk B))
  let b : U ⟶ U := torusUnitProjector k (Cor.mk (SmoothSite.product B G))
  let a' : V₀ ⟶ V₀ := γ (SmoothSite.productMap p (𝟙 G))
  let b' : V₀ ⟶ V₀ := γ (SmoothSite.productMap (𝟙 G) p)
  have ha : a ≫ f = f ≫ a' := doubleTorusComparison_inner k
  have hb : b ≫ f = f ≫ b' := doubleTorusComparison_outer k
  exact comp_complement_projectors f a b a' b' ha hb

omit [PerfectField k] [HasDerivedCategory (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory (SheafWithTransfers.{u + 1} k)] [HasDerivedCategory AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})] in
/-- The square of the complementary unit projector is the original double
reduced correspondence, with both factors kept in their actual order. -/
theorem exteriorProduct_torusComplement
    (hG : Cor.ExteriorGraphProduct k) :
    Cor.exteriorProduct
        (𝟙 ((Cor.graphFunctor k).obj G) - γ p)
        (𝟙 ((Cor.graphFunctor k).obj G) - γ p) =
      doubleTorusProjector k := by
  let F := Cor.graphFunctor k
  let t : G ⟶ G := p
  let A := F.obj G
  let a : A ⟶ A := F.map t
  let E := @Cor.exteriorProduct _ _ A A A A
  let g₁ := SmoothSite.productMap t (𝟙 G)
  let g₂ := SmoothSite.productMap (𝟙 G) t
  have eId : F.map (𝟙 G) = 𝟙 A := F.map_id G
  have h₁ : E a (𝟙 A) = F.map g₁ :=
    (congrArg (E a) eId.symm).trans (hG t (𝟙 G))
  have h₂ : E (𝟙 A) a = F.map g₂ :=
    (congrArg (fun b => E b a) eId.symm).trans (hG (𝟙 G) t)
  have h₃ : E a a = E a (𝟙 A) ≫ E (𝟙 A) a := by
    rw [h₁, h₂]
    have h : g₁ ≫ g₂ = SmoothSite.productMap t t := by
      change SmoothSite.productMap t (𝟙 G) ≫ SmoothSite.productMap (𝟙 G) t = _
      rw [← SmoothSite.productMap_comp, Category.comp_id, Category.id_comp]
    exact (hG t t).trans ((F.congr_map h.symm).trans (F.map_comp _ _))
  have hE : E (𝟙 _ - a) (𝟙 _ - a) =
      (E (𝟙 _) (𝟙 _) - E a (𝟙 _)) - (E (𝟙 _) a - E a a) := by
    rw [(E (𝟙 _ - a)).map_sub]
    have h₀ (b : Cor.mk G ⟶ Cor.mk G) : E (𝟙 _ - a) b = E (𝟙 _) b - E a b :=
      congrArg (fun f => f b) (E.map_sub (𝟙 _) a)
    exact congrArg₂ Sub.sub (h₀ (𝟙 A)) (h₀ a)
  let B₀ := Cor.tensorObj A A
  let u : B₀ ⟶ B₀ := F.map g₁
  let v : B₀ ⟶ B₀ := F.map g₂
  have hId : E (𝟙 A) (𝟙 A) = 𝟙 B₀ := Cor.exterior_id hG A A
  change E (𝟙 A - a) (𝟙 A - a) =
    (𝟙 B₀ - u) ≫ (𝟙 B₀ - v)
  change E a (𝟙 A) = u at h₁
  change E (𝟙 A) a = v at h₂
  rw [hE, h₃, h₁, h₂, hId]
  simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp, Category.comp_id]

omit [HasDerivedCategory AddCommGrpCat.{u + 1}] in
/-- The correspondence switch acts by minus one on the exact double reduced
projector, now expressed on the ordinary product of two tori. -/
theorem effectiveMotive_map_swap_comp_doubleTorusProjector :
    (M).map (γ (β_ G G).hom) ≫ (M).map (doubleTorusProjector k) =
      -(M).map (doubleTorusProjector k) := by
  let U := Cor.mk D
  let V₀ := Cor.mk V
  let F := Cor.graphFunctor k
  let H := effectiveMotive k
  let f : U ⟶ V₀ := F.map (doubleTorusComparison k)
  let i : H.obj U ⟶ H.obj V₀ := H.map f
  let a : U ⟶ U := torusDoubleSwap k (Cor.mk B)
  let a' : V₀ ⟶ V₀ := F.map (β_ G G).hom
  let b : U ⟶ U := torusDoubleReduction k (Cor.mk B)
  let b' : V₀ ⟶ V₀ := doubleTorusProjector k
  let : IsIso f := F.map_isIso _
  let hi : IsIso i := H.map_isIso f
  have h₀ : a ≫ f = f ≫ a' := by
    let s₀ := SmoothSite.productSwapLast B G G
    let s₁ := (β_ G G).hom
    let r := doubleTorusComparison k
    have hh : F.map s₀ ≫ f = f ≫ F.map s₁ :=
      (F.map_comp s₀ r).symm.trans
        ((F.congr_map (doubleTorusComparison_swap k)).trans (F.map_comp r s₁))
    exact hh
  have h₁ : H.map a ≫ i = i ≫ H.map a' :=
    (H.map_comp a f).symm.trans ((H.congr_map h₀).trans (H.map_comp f a'))
  have h₂ : H.map b ≫ i = i ≫ H.map b' :=
    (H.map_comp b f).symm.trans
      ((H.congr_map (doubleTorusComparison_projector k)).trans (H.map_comp f b'))
  have hw : H.map a ≫ H.map b = -H.map b :=
    (H.map_comp a b).symm.trans (effectiveMotive_map_torusDoubleSwap_comp_reduction k (Cor.mk B))
  change H.map a' ≫ H.map b' = -H.map b'
  have he : Epi i := @CategoryTheory.IsIso.epi_of_iso _ _ _ _ i hi
  have hcancel : i ≫ (H.map a' ≫ H.map b') = i ≫ (-H.map b') := by
    calc
      _ = H.map a ≫ H.map b ≫ i := by rw [← Category.assoc, ← h₁, Category.assoc, ← h₂]
      _ = -(H.map b ≫ i) := by rw [← Category.assoc, hw, Preadditive.neg_comp]
      _ = _ := by rw [h₂, Preadditive.comp_neg]
  exact he.1 _ _ hcancel

section Tensor

omit [Field k] [PerfectField k] [HasDerivedCategory (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory (SheafWithTransfers.{u + 1} k)] [HasDerivedCategory AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})]

variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C] [BraidedCategory C]
  {A L V₀ : C} (r : Retract L A) (e : A ⊗ A ≅ V₀) (s p₀ : V₀ ⟶ V₀)

/-- A signed switch on the ambient square becomes the identity on the
retract if the unshifted switch has sign minus one on its projector. -/
theorem braiding_eq_id_of_signed_retract
    (hβ : (β_ A A).hom ≫ e.hom = -(e.hom ≫ s))
    (hp : ((r.r ≫ r.i) ⊗ₘ (r.r ≫ r.i)) ≫ e.hom = e.hom ≫ p₀)
    (hs : s ≫ p₀ = -p₀) : (β_ L L).hom = 𝟙 _ := by
  let j := r.i ⊗ₘ r.i
  let q := r.r ⊗ₘ r.r
  have hsplit : j ≫ q = 𝟙 _ := by
    simp only [j, q, tensorHom_comp_tensorHom, r.retract, id_tensorHom_id]
  have hqp : q ≫ j ≫ e.hom = e.hom ≫ p₀ := by
    simpa only [← Category.assoc, j, q, tensorHom_comp_tensorHom] using hp
  have hβp : (β_ A A).hom ≫ q ≫ j ≫ e.hom = q ≫ j ≫ e.hom := by
    rw [hqp, ← Category.assoc, hβ, Preadditive.neg_comp, Category.assoc, hs,
      Preadditive.comp_neg, neg_neg]
  have hβq : (β_ A A).hom ≫ q = q := by
    have h := congrArg (fun f => f ≫ e.inv ≫ q) hβp
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, hsplit, Category.comp_id] using h
  calc
    (β_ L L).hom = (β_ L L).hom ≫ j ≫ q := by rw [hsplit, Category.comp_id]
    _ = j ≫ (β_ A A).hom ≫ q := (braiding_naturality_assoc r.i r.i q).symm
    _ = 𝟙 _ := by rw [hβq, hsplit]

end Tensor

end AlgebraicGeometry.MotivicHomotopy
