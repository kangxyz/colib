/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Chow.FlatComponentCoefficient
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.Stalks
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.ProductStalkLocalization
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ReducedProduct

/-!
# Residue tensor length at a generic product of closed subschemes

The exterior tensor of the two ambient residue fields, localized at the
actual product point, is the local ring of the literal product of the two
reduced point closures. Over a perfect field this product is reduced.
At a generic point of the original product of closed subschemes its
selected local ring is therefore a field. The general comparison retains its full
module length before imposing reducedness.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme
open scoped TensorProduct

universe u

namespace Stacks.Chow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {X Y P Q : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  (i : P ⟶ X) (j : Q ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
  (x : genericPoints (pullback (C := Scheme) (i ≫ f) (j ≫ g)))

local notation "a" => Scheme.Hom.productClosedMap f g i j
set_option quotPrecheck false in
local notation "w" => a x.val
local notation "p" => pullback.fst f g
local notation "q" => pullback.snd f g
local notation "I" => integralComponentAt (p w)
local notation "J" => integralComponentAt (q w)
set_option quotPrecheck false in
local notation "T" => pullback (C := Scheme) ((I).subschemeι ≫ f) ((J).subschemeι ≫ g)
set_option quotPrecheck false in
local notation "b" => Scheme.Hom.productClosedMap f g (I).subschemeι (J).subschemeι

private theorem range_reducedClosures_subset :
    Set.range b ⊆ Set.range a := by
  have hw : w ∈ Set.range a := Set.mem_range_self _
  rw [Scheme.Hom.productClosedMap, Scheme.Pullback.range_map] at hw
  have hi : closure ({p w} : Set X) ⊆ Set.range i :=
    closure_minimal (Set.singleton_subset_iff.mpr hw.1) i.isClosedEmbedding.isClosed_range
  have hj : closure ({q w} : Set Y) ⊆ Set.range j :=
    closure_minimal (Set.singleton_subset_iff.mpr hw.2) j.isClosedEmbedding.isClosed_range
  simp only [Scheme.Hom.productClosedMap, Scheme.Pullback.range_map,
    IdealSheafData.range_subschemeι, IdealSheafData.range_subschemeι,
    coe_support_integralComponentAt, coe_support_integralComponentAt]
  exact Set.inter_subset_inter (Set.preimage_mono hi) (Set.preimage_mono hj)

/-- A generic product point lies on the product of its two reduced point closures. -/
theorem exists_generic_reducedClosures :
    ∃ y : genericPoints T, b y.val = w := by
  have hw : w ∈ Set.range b := by
    unfold Scheme.Hom.productClosedMap
    rw [Scheme.Pullback.range_map, IdealSheafData.range_subschemeι,
      IdealSheafData.range_subschemeι, coe_support_integralComponentAt,
      coe_support_integralComponentAt]
    exact ⟨subset_closure (Set.mem_singleton _), subset_closure (Set.mem_singleton _)⟩
  obtain ⟨y, hy⟩ := hw
  refine ⟨⟨y, (mem_genericPoints_iff_forall_specializes_eq _).2 ?_⟩, hy⟩
  intro z hz
  have hzr := range_reducedClosures_subset f g i j x (Set.mem_range_self (f := b) z)
  obtain ⟨t, ht⟩ := hzr
  have htx : t ⤳ x.val := (a).isClosedEmbedding.isInducing.specializes_iff.mp <| by
    have h := hz.map (b).continuous
    exact (congrArg₂ Specializes ht.symm hy).mp h
  have h := (mem_genericPoints_iff_forall_specializes_eq _).1 x.property _ htx
  exact (b).isClosedEmbedding.injective (ht.symm.trans ((congrArg a h).trans hy.symm))

set_option quotPrecheck false in
local notation "A₀" => (X).presheaf.stalk (p w)
set_option quotPrecheck false in
local notation "B₀" => (Y).presheaf.stalk (q w)
set_option quotPrecheck false in
local notation "R₀" => (pullback f g).presheaf.stalk w

omit [IsClosedImmersion i] [IsClosedImmersion j] in
/-- Over any field, the localized exterior residue tensor has the length of the actual
local ring of the product of the reduced point closures. Nonreduced multiplicities are retained. -/
theorem length_extendExteriorResidueTensor_eq_length_stalk
    [Algebra k A₀] [Algebra k B₀]
    (φ : A₀ ⊗[k] B₀ →+* R₀)
    (hleft : φ.comp Algebra.TensorProduct.includeLeftRingHom = ((p).stalkMap w).hom)
    (hright : φ.comp Algebra.TensorProduct.includeRight.toRingHom = ((q).stalkMap w).hom)
    (y : genericPoints T) (hy : b y.val = w) :
    Module.length R₀ ((ModuleCat.extendScalars φ).obj
      (ModuleCat.exteriorTensorObj k (ModuleCat.of A₀ (IsLocalRing.ResidueField A₀))
        (ModuleCat.of B₀ (IsLocalRing.ResidueField B₀)))) =
      Module.length ((T).presheaf.stalk y.val) ((T).presheaf.stalk y.val) := by
  let e := exteriorQuotientsIsoTransportedClosedMapProductStalk f g
    (I).subschemeι (J).subschemeι w φ hleft hright y.val hy.symm
  rw [IdealSheafData.ker_subschemeι, IdealSheafData.ker_subschemeι,
    stalk_integralComponentAt_self, stalk_integralComponentAt_self] at e
  refine e.toLinearEquiv.length_eq.trans ?_
  let L := (T).presheaf.stalk y.val
  let ρ := transportedClosedStalkMap b y.val w hy.symm
  let M := (ModuleCat.restrictScalars ρ).obj (ModuleCat.of L L)
  let : Algebra R₀ L := ρ.toAlgebra
  let : IsScalarTower R₀ L M :=
    ⟨fun r s m => by
      change (ρ r * s) • m = ρ r • (s • m)
      exact mul_smul (ρ r) s m⟩
  have hρ : Function.Surjective ρ :=
    ((b).stalkMap_surjective y.val).comp <|
      ConcreteCategory.bijective_of_isIso
        (((pullback f g).presheaf.stalkCongr (.of_eq hy.symm)).hom) |>.surjective
  change Module.length R₀ M = Module.length L L
  exact Module.length_eq_of_surjective (R := L) (M := M) hρ

omit [IsClosedImmersion i] [IsClosedImmersion j] in
/-- The full ambient product-stalk length is the product of the input stalk lengths and
of the reduced-closures product multiplicity. No reducedness or perfectness is assumed. -/
theorem length_stalk_product_eq_mul_length_reducedClosures
    [Algebra k A₀] [Algebra k B₀]
    (φ : A₀ ⊗[k] B₀ →+* R₀) (hflat : φ.Flat)
    (hleft : φ.comp Algebra.TensorProduct.includeLeftRingHom = ((p).stalkMap w).hom)
    (hright : φ.comp Algebra.TensorProduct.includeRight.toRingHom = ((q).stalkMap w).hom)
    (y : genericPoints T) (hy : b y.val = w)
    (hA : IsFiniteLength A₀ A₀) (hB : IsFiniteLength B₀ B₀) :
    Module.length R₀ R₀ = Module.length A₀ A₀ * Module.length B₀ B₀ *
      Module.length ((T).presheaf.stalk y.val) ((T).presheaf.stalk y.val) := by
  let : Algebra (A₀ ⊗[k] B₀) R₀ := φ.toAlgebra
  let : Module.Flat (A₀ ⊗[k] B₀) R₀ := RingHom.flat_algebraMap_iff.mp hflat
  have h := ModuleCat.Tor.length_self_eq_mul_length_extendExteriorResidueTensor
    (k := k) (S := R₀) hA hB
  simp only [RingHom.algebraMap_toAlgebra] at h
  rw [length_extendExteriorResidueTensor_eq_length_stalk f g i j x φ hleft hright y hy] at h
  exact h

/-- For generic labels in the two factors, the product's stalk length is the two
input multiplicities times the stalk length of their actual reduced-closure product.
The projection equations ensure that the same labels and points occur in all three factors. -/
theorem length_stalk_product_at_generic_closures
    (α : genericPoints X) (β : genericPoints Y)
    (z : genericPoints (pullback (C := Scheme) ((integralComponentAt α.val).subschemeι ≫ f)
      ((integralComponentAt β.val).subschemeι ≫ g)))
    (hα : pullback.fst f g
      (Scheme.Hom.productClosedMap f g (integralComponentAt α.val).subschemeι
        (integralComponentAt β.val).subschemeι z.val) = α.val)
    (hβ : pullback.snd f g
      (Scheme.Hom.productClosedMap f g (integralComponentAt α.val).subschemeι
        (integralComponentAt β.val).subschemeι z.val) = β.val)
    (hA : IsFiniteLength (X.presheaf.stalk α.val) (X.presheaf.stalk α.val))
    (hB : IsFiniteLength (Y.presheaf.stalk β.val) (Y.presheaf.stalk β.val)) :
    let C := pullback (C := Scheme) ((integralComponentAt α.val).subschemeι ≫ f)
      ((integralComponentAt β.val).subschemeι ≫ g)
    let point := Scheme.Hom.productClosedMap f g (integralComponentAt α.val).subschemeι
      (integralComponentAt β.val).subschemeι z.val
    Module.length ((pullback f g).presheaf.stalk point) ((pullback f g).presheaf.stalk point) =
      Module.length (X.presheaf.stalk α.val) (X.presheaf.stalk α.val) *
        Module.length (Y.presheaf.stalk β.val) (Y.presheaf.stalk β.val) *
          Module.length (C.presheaf.stalk z.val) (C.presheaf.stalk z.val) := by
  dsimp only
  let point := Scheme.Hom.productClosedMap f g (integralComponentAt α.val).subschemeι
    (integralComponentAt β.val).subschemeι z.val
  let A := X.presheaf.stalk (pullback.fst f g point)
  let B := Y.presheaf.stalk (pullback.snd f g point)
  let R := (pullback f g).presheaf.stalk point
  let : Algebra k A := BaseChangeStalk.stalkAlgebraOfField f (pullback.fst f g point)
  let : Algebra k B := BaseChangeStalk.stalkAlgebraOfField g (pullback.snd f g point)
  obtain ⟨φ, hleft, hright, S, hS⟩ :=
    BaseChangeStalk.pullback_stalk_isLocalization_overField f g point
  let : Algebra (A ⊗[k] B) R := φ.toAlgebra
  let : IsLocalization S R := hS
  let : Module.Flat (A ⊗[k] B) R := IsLocalization.flat R S
  have hflat : φ.Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have H := length_stalk_product_eq_mul_length_reducedClosures f g
    (integralComponentAt α.val).subschemeι (integralComponentAt β.val).subschemeι
    z φ hflat hleft hright
  dsimp only [point] at H
  rw [hα, hβ] at H
  exact H z rfl hA hB

/-- Reducedness of the actual product of point closures suffices for residue tensor length one. -/
theorem length_extendExteriorResidueTensor_at_genericClosedProduct_of_isReduced
    [IsReduced T] [Algebra k A₀] [Algebra k B₀]
    (φ : A₀ ⊗[k] B₀ →+* R₀)
    (hleft : φ.comp Algebra.TensorProduct.includeLeftRingHom = ((p).stalkMap w).hom)
    (hright : φ.comp Algebra.TensorProduct.includeRight.toRingHom = ((q).stalkMap w).hom) :
    Module.length R₀ ((ModuleCat.extendScalars φ).obj
      (ModuleCat.exteriorTensorObj k (ModuleCat.of A₀ (IsLocalRing.ResidueField A₀))
        (ModuleCat.of B₀ (IsLocalRing.ResidueField B₀)))) = 1 := by
  obtain ⟨y, hy⟩ := exists_generic_reducedClosures f g i j x
  rw [length_extendExteriorResidueTensor_eq_length_stalk f g i j x φ hleft hright y hy]
  let L := (T).presheaf.stalk y.val
  let : Field L := (isField_stalk_of_closure_mem_irreducibleComponents T y.val y.property).toField
  exact Module.length_eq_one_iff.mpr (inferInstance : IsSimpleModule L L)

/-- The perfect-field specialization of the general residue tensor length comparison. -/
theorem length_extendExteriorResidueTensor_at_genericClosedProduct
    [PerfectField k] [Algebra k A₀] [Algebra k B₀]
    (φ : A₀ ⊗[k] B₀ →+* R₀)
    (hleft : φ.comp Algebra.TensorProduct.includeLeftRingHom = ((p).stalkMap w).hom)
    (hright : φ.comp Algebra.TensorProduct.includeRight.toRingHom = ((q).stalkMap w).hom) :
    Module.length R₀ ((ModuleCat.extendScalars φ).obj
      (ModuleCat.exteriorTensorObj k (ModuleCat.of A₀ (IsLocalRing.ResidueField A₀))
        (ModuleCat.of B₀ (IsLocalRing.ResidueField B₀)))) = 1 := by
  let : IsIntegral (I).subscheme := isIntegral_integralComponentAt (p w)
  let : IsIntegral (J).subscheme := isIntegral_integralComponentAt (q w)
  let : IsReduced T := isReduced_pullback_over_perfectField ((I).subschemeι ≫ f)
    ((J).subschemeι ≫ g)
  exact length_extendExteriorResidueTensor_at_genericClosedProduct_of_isReduced
    f g i j x φ hleft hright

end Stacks.Chow
