/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Algebra.Category.ModuleCat.Tor.ExteriorQuotient
public import Colib.RingTheory.Tor.ExteriorEuler.Length
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Quotient modules as exterior tensor products

The factorwise action of the tensor product ring on the two quotient modules agrees
with the action in the existing product-ideal quotient theorem. This identifies the
exterior tensor with that quotient, including after scalar extension.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace ModuleCat.Tor

universe u

variable {k A B : Type u} [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

attribute [local instance] Stacks.Intersection.Diagonal.exteriorModule

/-- The two presentations of the factorwise action on the tensor of quotient modules agree
via the map fixing each pure tensor. -/
def exteriorTensorObjQuotientActionIso (I : Ideal A) (J : Ideal B) :
    ModuleCat.exteriorTensorObj k (ModuleCat.of A (A ⧸ I)) (ModuleCat.of B (B ⧸ J)) ≅
      ModuleCat.of (A ⊗[k] B) ((A ⧸ I) ⊗[k] (B ⧸ J)) :=
  let X := ModuleCat.exteriorTensorObj k (ModuleCat.of A (A ⧸ I)) (ModuleCat.of B (B ⧸ J))
  let Y := ModuleCat.of (A ⊗[k] B) ((A ⧸ I) ⊗[k] (B ⧸ J))
  let quotientRestrict {R : Type u} [CommRing R] [Algebra k R] (P : Ideal R) :
      ((ModuleCat.restrictScalars (algebraMap k R)).obj (ModuleCat.of R (R ⧸ P))) ≃ₗ[k]
        R ⧸ P := by
    let M := (ModuleCat.restrictScalars (algebraMap k R)).obj (ModuleCat.of R (R ⧸ P))
    exact @AddEquiv.toLinearEquiv k M (R ⧸ P) _ M.isAddCommGroup.toAddCommMonoid
      _ M.isModule _ (AddEquiv.refl (R ⧸ P)) fun a x =>
        IsScalarTower.algebraMap_smul R a (show R ⧸ P from x)
  let e : X ≃+ Y := (TensorProduct.congr (quotientRestrict I) (quotientRestrict J)).toAddEquiv
  letI : Module (A ⊗[k] B) X := X.isModule
  letI : Module (A ⊗[k] B) Y := Y.isModule
  have h (r : A ⊗[k] B) (x : X) : e (r • x) = r • e x := by
    have hadd (x y : X) : e (x + y) = e x + e y := e.map_add x y
    induction r using TensorProduct.inductionOn with
    | add r s hr hs => rw [add_smul, hadd, hr, hs, add_smul]
    | tmul a b =>
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => rw [smul_add, hadd, hx, hy, hadd, smul_add]
      | tmul m n => rfl
  @LinearEquiv.toModuleIso (A ⊗[k] B) _ X Y X.isAddCommGroup Y.isAddCommGroup
    X.isModule Y.isModule
    (@AddEquiv.toLinearEquiv (A ⊗[k] B) X Y _ X.isAddCommGroup.toAddCommMonoid
      Y.isAddCommGroup.toAddCommMonoid X.isModule Y.isModule e h)

/-- The exterior tensor of two quotient modules is the quotient by their product ideal. -/
def exteriorTensorObjQuotientIso (I : Ideal A) (J : Ideal B) :
    ModuleCat.exteriorTensorObj k (ModuleCat.of A (A ⧸ I)) (ModuleCat.of B (B ⧸ J)) ≅
      ModuleCat.of (A ⊗[k] B) ((A ⊗[k] B) ⧸ productIdeal (k := k) I J) :=
  exteriorTensorObjQuotientActionIso (k := k) I J ≪≫ productQuotientIso I J

/-- Scalar extension of the exterior tensor of two quotients is the quotient by the extended
product ideal. -/
def extendExteriorTensorObjQuotientIso {S : Type u} [CommRing S]
    (φ : (A ⊗[k] B) →+* S) (I : Ideal A) (J : Ideal B) :
    (ModuleCat.extendScalars φ).obj
        (ModuleCat.exteriorTensorObj k (ModuleCat.of A (A ⧸ I)) (ModuleCat.of B (B ⧸ J))) ≅
      ModuleCat.of S (S ⧸ (productIdeal (k := k) I J).map φ) :=
  (ModuleCat.extendScalars φ).mapIso (exteriorTensorObjQuotientActionIso (k := k) I J) ≪≫
    extendProductQuotientIso φ I J

/-- The self-length after flat base change of a tensor algebra retains the residue-tensor
multiplicity. The two local input algebras need only have finite self-length. -/
theorem length_self_eq_mul_length_extendExteriorResidueTensor {S : Type u} [CommRing S]
    [IsLocalRing A] [IsLocalRing B] [Algebra (A ⊗[k] B) S]
    [Module.Flat (A ⊗[k] B) S]
    (hA : IsFiniteLength A A) (hB : IsFiniteLength B B) :
    Module.length S S = Module.length A A * Module.length B B *
      Module.length S ((ModuleCat.extendScalars (algebraMap (A ⊗[k] B) S)).obj
        (ModuleCat.exteriorTensorObj k (ModuleCat.of A (IsLocalRing.ResidueField A))
          (ModuleCat.of B (IsLocalRing.ResidueField B)))) := by
  let φ := algebraMap (A ⊗[k] B) S
  have hA' := (AlgEquiv.quotientBot A A).symm.toLinearEquiv.isFiniteLength hA
  have hB' := (AlgEquiv.quotientBot B B).symm.toLinearEquiv.isFiniteLength hB
  have h := ModuleCat.length_extendScalars_exteriorTensor (k := k) (S := S)
    (ModuleCat.of A (A ⧸ (⊥ : Ideal A))) (ModuleCat.of B (B ⧸ (⊥ : Ideal B))) hA' hB'
  have hI : (productIdeal (k := k) (⊥ : Ideal A) (⊥ : Ideal B)).map φ = ⊥ := by
    simp only [productIdeal, Ideal.map_bot, bot_sup_eq]
  let e := extendExteriorTensorObjQuotientIso (k := k) φ (⊥ : Ideal A) (⊥ : Ideal B) ≪≫
    (Ideal.quotientEquivAlgOfEq S hI).toLinearEquiv.toModuleIso ≪≫
      (AlgEquiv.quotientBot S S).toLinearEquiv.toModuleIso
  have he := e.toLinearEquiv.length_eq
  rw [he, (AlgEquiv.quotientBot A A).toLinearEquiv.length_eq,
    (AlgEquiv.quotientBot B B).toLinearEquiv.length_eq] at h
  exact h

/-- The extended residue tensor has finite length if its defining ideal has the maximal ideal
as a minimal prime. -/
theorem length_extendExteriorResidueTensor_ne_top {S : Type u} [CommRing S]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing S] [IsNoetherianRing S]
    (φ : (A ⊗[k] B) →+* S)
    (h : IsLocalRing.maximalIdeal S ∈
      ((productIdeal (k := k) (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal B)).map
        φ).minimalPrimes) :
    Module.length S ((ModuleCat.extendScalars φ).obj
      (ModuleCat.exteriorTensorObj k (ModuleCat.of A (IsLocalRing.ResidueField A))
        (ModuleCat.of B (IsLocalRing.ResidueField B)))) ≠ ⊤ := by
  let I := (productIdeal (k := k) (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal B)).map φ
  have : IsArtinianRing (S ⧸ I) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I h
  rw [(show ((ModuleCat.extendScalars φ).obj
      (ModuleCat.exteriorTensorObj k (ModuleCat.of A (IsLocalRing.ResidueField A))
        (ModuleCat.of B (IsLocalRing.ResidueField B)))) ≅ ModuleCat.of S (S ⧸ I) from
    extendExteriorTensorObjQuotientIso (k := k) φ (IsLocalRing.maximalIdeal A)
      (IsLocalRing.maximalIdeal B)).toLinearEquiv.length_eq]
  change Module.length S (S ⧸ I) ≠ ⊤
  rw [Module.length_eq_of_surjective (R := S ⧸ I) Ideal.Quotient.mk_surjective]
  exact Module.length_ne_top

end ModuleCat.Tor
