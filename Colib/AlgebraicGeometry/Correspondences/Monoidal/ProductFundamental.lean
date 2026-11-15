/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Chow.FlatComponentCoefficient
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.ProductIdeal
import Colib.AlgebraicGeometry.Chow.FiniteOpenRestriction
import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.GenericPoints

/-!
# A fundamental cycle on a product over a field

Each generic point of the product lies over a unique generic point of
the first factor. Its contribution to the product fundamental cycle is
the original local length times the cycle of the full inverse image of
that component. The original closed immersions are kept throughout.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme Function.locallyFinsuppWithin

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k] {A B : Scheme.{u}}
  (a : A ⟶ Spec (.of k)) (b : B ⟶ Spec (.of k))
  [IsNoetherian A] [IsNoetherian B] [LocallyOfFiniteType a] [LocallyOfFiniteType b]
  [QuasiCompact a] [QuasiCompact b]

local notation "P" => (pullback a b : Scheme)
local notation "π" => pullback.fst a b

/-- The inclusion into the fiber product obtained from the integral component of the
first factor at the given point. -/
def componentProductInclusion (x : A) :
    pullback ((integralComponentAt x).subschemeι ≫ a) b ⟶ P :=
  pullback.map _ _ _ _ (integralComponentAt x).subschemeι (𝟙 B) (𝟙 _) (by simp) (by simp)

instance componentProductInclusion_isClosedImmersion (x : A) :
    IsClosedImmersion (componentProductInclusion a b x) := by
  change IsClosedImmersion
    (Scheme.Hom.productClosedMap a b (integralComponentAt x).subschemeι (𝟙 B))
  infer_instance

omit [AlgebraicGeometry.IsNoetherian A] [AlgebraicGeometry.IsNoetherian B]
  [LocallyOfFiniteType a] [LocallyOfFiniteType b] [QuasiCompact a] [QuasiCompact b] in
private theorem range_componentProductInclusion (x : A) :
    Set.range (componentProductInclusion a b x) = (π) ⁻¹' closure ({x} : Set A) := by
  unfold componentProductInclusion
  have h : Set.range (𝟙 B : B ⟶ B) = Set.univ := by
    change Set.range (id : B → B) = _
    exact Set.range_id
  rw [Scheme.Pullback.range_map, h, Set.preimage_univ, Set.inter_univ,
    Scheme.IdealSheafData.range_subschemeι, coe_support_integralComponentAt]

omit [AlgebraicGeometry.IsNoetherian A] [AlgebraicGeometry.IsNoetherian B]
  [LocallyOfFiniteType a] [LocallyOfFiniteType b] [QuasiCompact a] [QuasiCompact b] in
private theorem componentProductInclusion_generic (x : genericPoints A)
    (t : genericPoints (pullback ((integralComponentAt x.val).subschemeι ≫ a) b : Scheme.{u})) :
    componentProductInclusion a b x.val t.val ∈ genericPoints P := by
  let p := componentProductInclusion a b x.val
  let U := (integralComponentAt x.val).subscheme
  let q := pullback.fst ((integralComponentAt x.val).subschemeι ≫ a) b
  let : IsIntegral U := isIntegral_integralComponentAt x.val
  have hq : q t.val = genericPoint U := by
    have h := mem_genericPoints_of_flat q t.property
    simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using h
  have hw : p ≫ π = q ≫ (integralComponentAt x.val).subschemeι := pullback.lift_fst _ _ _
  have hx : π (p t.val) = x.val := by
    rw [← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply, hq]
    exact genericPointOf_integralComponentAt x.val
  apply mem_genericPoints_of_forall_specializes_eq
  intro z hz
  have hπ : π z = x.val :=
    forall_specializes_eq_of_mem_genericPoints x.property _ (hx ▸ hz.map (π).continuous)
  obtain ⟨y, rfl⟩ : z ∈ Set.range p := by
    rw [range_componentProductInclusion]
    change π z ∈ closure ({x.val} : Set A)
    rw [hπ]
    exact subset_closure (Set.mem_singleton x.val)
  exact congrArg p (forall_specializes_eq_of_mem_genericPoints t.property y
    (p.isClosedEmbedding.isInducing.specializes_iff.mp hz))

omit [AlgebraicGeometry.IsNoetherian B] in
/-- The fundamental cycle of the whole product is the sum of the pushforwards
of the full inverse images of the generic components of the first factor. -/
theorem fundamentalCycle_product_eq_sum_components [Fintype (genericPoints A)] :
    letI : IsNoetherian P := Scheme.isNoetherian_of_finiteType_of_isNoetherian (π ≫ a)
    letI : ∀ x : genericPoints A, IsNoetherian
        (pullback ((integralComponentAt x.val).subschemeι ≫ a) b) := fun x =>
      Scheme.isNoetherian_of_finiteType_of_isNoetherian
        (pullback.fst _ b ≫ (integralComponentAt x.val).subschemeι ≫ a)
    AlgebraicCycle.fundamentalCycle P =
      ∑ x : genericPoints A, (AlgebraicCycle.fundamentalCycle A x.val) •
        finiteCyclePushforward (componentProductInclusion a b x.val)
          (AlgebraicCycle.fundamentalCycle _) := by
  classical
  let : IsNoetherian P := Scheme.isNoetherian_of_finiteType_of_isNoetherian (π ≫ a)
  let : ∀ x : genericPoints A, IsNoetherian
      (pullback ((integralComponentAt x.val).subschemeι ≫ a) b) := fun x =>
    Scheme.isNoetherian_of_finiteType_of_isNoetherian
      (pullback.fst _ b ≫ (integralComponentAt x.val).subschemeι ≫ a)
  let : ∀ x : genericPoints A, IsNoetherian
      ((integralComponentAt x.val).comap π).subscheme := fun x =>
    Scheme.isNoetherian_of_finiteType_of_isNoetherian
      ((integralComponentAt x.val).comap π).subschemeι
  have hchange (x : genericPoints A) :
      finiteCyclePushforward (componentProductInclusion a b x.val)
          (AlgebraicCycle.fundamentalCycle _) =
        finiteCyclePushforward ((integralComponentAt x.val).comap π).subschemeι
          (AlgebraicCycle.fundamentalCycle _) := by
    let I := integralComponentAt x.val
    let f := π
    let j := componentProductInclusion a b x.val
    have hker : j.ker = I.comap f := by
      unfold j componentProductInclusion
      change (Scheme.Hom.productClosedMap a b I.subschemeι (𝟙 B)).ker = _
      rw [Scheme.Hom.productClosedMap_ker, Scheme.IdealSheafData.ker_subschemeι,
        Scheme.Hom.ker_eq_bot_of_isIso]
      simp [f]
    let v := IsClosedImmersion.lift ((I.comap f).subschemeι) j
      (by rw [Scheme.IdealSheafData.ker_subschemeι, hker])
    have hv : v ≫ (I.comap f).subschemeι = j := IsClosedImmersion.lift_fac _ _ _
    let : IsIso v := IsClosedImmersion.isIso_of_ker_eq j _ v hv
      (by simpa [Scheme.IdealSheafData.ker_subschemeι] using hker)
    rw [← finiteCyclePushforward_fundamentalCycle_iso (asIso v), finiteCyclePushforward_comp_apply]
    exact finiteCyclePushforward_congr _ _ hv.symm _
  apply Function.locallyFinsuppWithin.ext
  intro z
  by_cases hz : z ∈ genericPoints P
  · simp only [coe_sum, Finset.sum_apply, coe_zsmul, Pi.smul_apply, smul_eq_mul]
    simp_rw [hchange]
    have h := fundamentalCycle_apply_eq_sum_flat_components π ⟨z, hz⟩
    simpa only [AlgebraicCycle.fundamentalCycle_apply_generic] using h
  · rw [AlgebraicCycle.fundamentalCycle_apply_of_notMem _ z hz]
    simp only [coe_sum, Finset.sum_apply, coe_zsmul, Pi.smul_apply, smul_eq_mul]
    symm
    apply Finset.sum_eq_zero
    intro x _
    have hzero : finiteCyclePushforward (componentProductInclusion a b x.val)
        (AlgebraicCycle.fundamentalCycle _) z = 0 := by
      by_contra hn
      obtain ⟨t, ht, rfl⟩ := finiteCyclePushforward_support_subset _ _ hn
      exact hz (componentProductInclusion_generic a b x
        ⟨t, AlgebraicCycle.support_fundamentalCycle_subset _ ht⟩)
    rw [hzero, mul_zero]

end Stacks.Chow
