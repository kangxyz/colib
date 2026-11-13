/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCutParameter.Compare
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCut.Admissibility
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Parameter
import Colib.AlgebraicGeometry.PresheavesWithTransfers.ContractionHI
import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.CylinderNaturality

/-!
# Precomposition of a power cut by a finite transfer

The two power graphs commute with the original exterior transfer. Unit
precomposition then commutes with the transfer by native parameter
naturality. The result is Voevodsky's Lemma 4.4 for all sufficiently large
exponents on the native smooth site.
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Stacks.Chow

universe u v

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme SmoothSite SmoothSite.Contraction

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "T" => multiplicativeGroupObject Sₖ
local notation "F" => Cor.parameterProduct T
local notation "G(" X ")" => product X T
local notation "V(" Y ")" => torusPowerCutRetainedTarget k Y
local notation "γ" => CategoryTheory.Functor.map (graphFunctor k)

variable {U X Y : SmoothSite (Spec (.of k))}

/-- The original unit section commutes with an arbitrary native transfer. -/
@[reassoc]
theorem nativeTorusUnitSection_graph_naturality (β : Cor.mk U ⟶ Cor.mk X) :
    γ (unitSection.app U) ≫ (F).map β = β ≫ γ (unitSection.app X) := by
  let B := SmoothSite.base Sₖ
  let : GeometricallyIntegral B.hom :=
    PresheafWithTransfers.base_geometricallyIntegral (k := k)
  let eU := (graphFunctor k).mapIso (productBaseIso U)
  let eX := (graphFunctor k).mapIso (productBaseIso X)
  have hp : (parameterProduct B).map β ≫ eX.hom = eU.hom ≫ β :=
    parameterProduct_projection_naturality U X B β
  have hi : eU.inv ≫ (parameterProduct B).map β = β ≫ eX.inv := by
    calc
      _ = eU.inv ≫ ((parameterProduct B).map β ≫ eX.hom) ≫ eX.inv := by
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      _ = _ := by rw [hp, Category.assoc, Iso.inv_hom_id_assoc]
  have hU : γ (unitSection.app U) =
      eU.inv ≫ (parameterProductMap (torusOne Sₖ)).app (Cor.mk U) := by
    change _ = γ (productBaseIso U).inv ≫ γ (SmoothSite.productMap (𝟙 U) (torusOne Sₖ))
    rw [← Functor.map_comp, baseProduct_unit]
  have hX : γ (unitSection.app X) =
      eX.inv ≫ (parameterProductMap (torusOne Sₖ)).app (Cor.mk X) := by
    change _ = γ (productBaseIso X).inv ≫ γ (SmoothSite.productMap (𝟙 X) (torusOne Sₖ))
    rw [← Functor.map_comp, baseProduct_unit]
  rw [hU, hX, Category.assoc, ← (parameterProductMap (torusOne Sₖ)).naturality β,
    ← Category.assoc, hi, Category.assoc]

private theorem parameterUnitCut_precomp (β : Cor.mk U ⟶ Cor.mk X)
    (a : Cor.mk (G(X)) ⟶ Cor.mk (V(Y))) :
    torusPowerParameterUnitCut k U Y ((F).map β ≫ a) =
      β ≫ torusPowerParameterUnitCut k X Y a := by
  let u₀ : Cor.mk U ⟶ Cor.mk (G(U)) := γ (unitSection.app U)
  let u₁ : Cor.mk X ⟶ Cor.mk (G(X)) := γ (unitSection.app X)
  let b : Cor.mk (G(U)) ⟶ Cor.mk (G(X)) := (F).map β
  let p : Cor.mk (V(Y)) ⟶ Cor.mk Y := γ (torusPowerParameterForget k Y)
  rw [torusPowerParameterUnitCut_apply, torusPowerParameterUnitCut_apply]
  change u₀ ≫ (b ≫ a) ≫ p = β ≫ u₁ ≫ a ≫ p
  calc
    _ = u₀ ≫ b ≫ a ≫ p :=
      congrArg (fun m => u₀ ≫ m) (Category.assoc b a p)
    _ = (u₀ ≫ b) ≫ a ≫ p := (Category.assoc u₀ b (a ≫ p)).symm
    _ = (β ≫ u₁) ≫ a ≫ p :=
      congrArg (fun m => m ≫ a ≫ p) (nativeTorusUnitSection_graph_naturality k β)
    _ = _ := Category.assoc β u₁ (a ≫ p)

local notation "uᵧ" => torusPowerParameterTargetUnit k Y

/-- The fixed-exponent identity with the actual admissibility witnesses on
both cuts. The two retained graph domains supply the parameter comparison. -/
theorem torusPowerCut_comp_of_parameterGraphs
    (β : Cor.mk U ⟶ Cor.mk X) (a : Cor.mk (G(X)) ⟶ Cor.mk (G(Y))) (n : ℕ)
    (ha : a ∈ torusPowerCutDomain k X Y n)
    (ha' : (F).map β ≫ a ∈ torusPowerCutDomain k U Y n)
    (h₁ : a ∈ torusPowerParameterGraphDomain k X Y (n + 1) 1)
    (h₂ : a ∈ torusPowerParameterGraphDomain k X Y (n + 1) uᵧ) :
    torusPowerCut k U Y n ⟨(F).map β ≫ a, ha'⟩ = β ≫ torusPowerCut k X Y n ⟨a, ha⟩ := by
  let a' : Cor.mk (G(U)) ⟶ Cor.mk (G(Y)) := (F).map β ≫ a
  change torusPowerCut k U Y n ⟨a', ha'⟩ = _
  obtain ⟨h₁', hc₁⟩ := torusPowerParameterGraph_comp k X Y (n + 1) 1 U β ⟨a, h₁⟩
  obtain ⟨h₂', hc₂⟩ := torusPowerParameterGraph_comp k X Y (n + 1) uᵧ U β ⟨a, h₂⟩
  change a' ∈ torusPowerParameterGraphDomain k U Y (n + 1) 1 at h₁'
  change a' ∈ torusPowerParameterGraphDomain k U Y (n + 1) uᵧ at h₂'
  change torusPowerParameterGraph k U Y (n + 1) 1 ⟨a', h₁'⟩ =
    (F).map β ≫ torusPowerParameterGraph k X Y (n + 1) 1 ⟨a, h₁⟩ at hc₁
  change torusPowerParameterGraph k U Y (n + 1) uᵧ ⟨a', h₂'⟩ =
    (F).map β ≫ torusPowerParameterGraph k X Y (n + 1) uᵧ ⟨a, h₂⟩ at hc₂
  rw [torusPowerCut_eq_parameterUnitCut_sub k U Y n ⟨a', ha'⟩ h₁' h₂',
    torusPowerCut_eq_parameterUnitCut_sub k X Y n ⟨a, ha⟩ h₁ h₂, hc₁, hc₂]
  simp only [parameterUnitCut_precomp, Preadditive.comp_sub]

/-- For every sufficiently large exponent both native cuts are admissible
and commute with the original finite correspondence. -/
theorem exists_torusPowerCut_comp
    (β : Cor.mk U ⟶ Cor.mk X) (a : Cor.mk (G(X)) ⟶ Cor.mk (G(Y))) :
    let a' : Cor.mk (G(U)) ⟶ Cor.mk (G(Y)) := (F).map β ≫ a
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      a ∈ torusPowerCutDomain k X Y n ∧ a' ∈ torusPowerCutDomain k U Y n ∧
      ∀ (ha : a ∈ torusPowerCutDomain k X Y n) (ha' : a' ∈ torusPowerCutDomain k U Y n),
        torusPowerCut k U Y n ⟨a', ha'⟩ = β ≫ torusPowerCut k X Y n ⟨a, ha⟩ := by
  let a' : Cor.mk (G(U)) ⟶ Cor.mk (G(Y)) := (F).map β ≫ a
  change ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a ∈ torusPowerCutDomain k X Y n ∧ _
  obtain ⟨N₁, h₁⟩ := exists_mem_torusPowerCutDomain k X Y a
  obtain ⟨N₂, h₂⟩ := exists_mem_torusPowerCutDomain k U Y a'
  obtain ⟨N₃, h₃⟩ := eventually_mem_torusPowerParameterGraphDomain k X Y 1 a
  obtain ⟨N₄, h₄⟩ := eventually_mem_torusPowerParameterGraphDomain k X Y uᵧ a
  let N := max (max N₁ N₂) (max N₃ N₄)
  refine ⟨N, fun n hn => ⟨h₁ n ?_, h₂ n ?_, fun ha ha' => ?_⟩⟩
  · exact (le_max_left N₁ N₂).trans ((le_max_left _ _).trans hn)
  · exact (le_max_right N₁ N₂).trans ((le_max_left _ _).trans hn)
  · have hN : max N₃ N₄ ≤ n + 1 := (le_max_right _ _).trans (hn.trans (Nat.le_succ n))
    exact torusPowerCut_comp_of_parameterGraphs k β a n ha ha'
      (h₃ _ ((le_max_left _ _).trans hN)) (h₄ _ ((le_max_right _ _).trans hN))

/-- A finite family of transfer comparisons has a common eventual exponent. -/
theorem exists_torusPowerCut_comp_family {ι : Type v} [Finite ι]
    (U₀ X₀ Y₀ : ι → SmoothSite Sₖ)
    (β₀ : ∀ i, Cor.mk (U₀ i) ⟶ Cor.mk (X₀ i))
    (a₀ : ∀ i, Cor.mk (G(X₀ i)) ⟶ Cor.mk (G(Y₀ i))) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ i,
      a₀ i ∈ torusPowerCutDomain k (X₀ i) (Y₀ i) n ∧
      (F).map (β₀ i) ≫ a₀ i ∈ torusPowerCutDomain k (U₀ i) (Y₀ i) n ∧
      ∀ (ha : a₀ i ∈ torusPowerCutDomain k (X₀ i) (Y₀ i) n)
        (ha' : (F).map (β₀ i) ≫ a₀ i ∈ torusPowerCutDomain k (U₀ i) (Y₀ i) n),
        torusPowerCut k (U₀ i) (Y₀ i) n ⟨(F).map (β₀ i) ≫ a₀ i, ha'⟩ =
          β₀ i ≫ torusPowerCut k (X₀ i) (Y₀ i) n ⟨a₀ i, ha⟩ := by
  classical
  let : Fintype ι := Fintype.ofFinite _
  choose N hN using fun i => exists_torusPowerCut_comp k (β₀ i) (a₀ i)
  refine ⟨Finset.univ.sup N, fun n hn i => ?_⟩
  exact hN i n ((Finset.le_sup (Finset.mem_univ i)).trans hn)

end AlgebraicGeometry.Cor
