/-
Copyright (c) 2026 Colib contributors and AxiomMath/Stacks contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ResidueField.FieldPoint
public import Colib.AlgebraicGeometry.Morphisms.Frobenius.IteratedNaturality
public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import Mathlib.Algebra.CharP.IntermediateField

/-!
# Finite field-valued points after actual iterated relative Frobenius

A finite extension is purely inseparable of bounded exponent over its native separable
closure. The corresponding power map factors a field-valued point through the spectrum
of that actual separable closure on the native iterated Frobenius twist. This constructs
a marked point factorization, not an abstract equivalent target or field-change category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Frobenius

universe u

namespace AlgebraicGeometry

/-- The original finite field-valued point factors through the native separable closure
on an actual iterated Frobenius twist, with both the base map and marked factorization. -/
theorem exists_separableFieldPoint_nFoldRelativeFrobenius
    {k L : Type u} [Field k] [Field L] [Algebra k L] [Module.Finite k L]
    (p : ℕ) [Fact p.Prime] [CharP k p] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (a : Spec (.of L) ⟶ X)
    (ha : a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k L))) :
    ∃ (n : ℕ) (b : Spec (.of (separableClosure k L)) ⟶
        (nFoldFrobeniusTwist (Spec (.of k)) p (isInCharacteristic_spec k p) n
          (Over.mk f)).left),
      b ≫ (nFoldFrobeniusTwist (Spec (.of k)) p (isInCharacteristic_spec k p) n
        (Over.mk f)).hom =
          Spec.map (CommRingCat.ofHom (algebraMap k (separableClosure k L))) ∧
      Spec.map (CommRingCat.ofHom (algebraMap (separableClosure k L) L)) ≫ b =
        a ≫ (nFoldRelativeFrobenius (Spec (.of k)) p (isInCharacteristic_spec k p) n
          (Over.mk f)).left := by
  let K := separableClosure k L
  let : CharP L p := charP_of_injective_algebraMap (algebraMap k L).injective p
  let : CharP K p := inferInstance
  let n := IsPurelyInseparable.exponent K L
  let φ : L →+* K := IsPurelyInseparable.iterateFrobenius K L p (n := n) le_rfl
  have hφ (z : L) : algebraMap K L (φ z) = z ^ p ^ n :=
    IsPurelyInseparable.algebraMap_iterateFrobenius K p le_rfl z
  have hscalar : φ.comp (algebraMap k L) =
      (algebraMap k K).comp (_root_.iterateFrobenius k p n) := by
    apply RingHom.ext
    intro z
    apply (algebraMap K L).injective
    change algebraMap K L (φ (algebraMap k L z)) =
      algebraMap K L (algebraMap k K (_root_.iterateFrobenius k p n z))
    rw [hφ, ← IsScalarTower.algebraMap_apply k K L, iterateFrobenius_def, map_pow]
  have hw : (Spec.map (CommRingCat.ofHom φ) ≫ a) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫
        absoluteFrobeniusPow (Spec (.of k)) p (isInCharacteristic_spec k p) n := by
    rw [Category.assoc, ha, absoluteFrobeniusPow_spec, ← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun h : k →+* K => Spec.map (CommRingCat.ofHom h)) hscalar
  let b := pullback.lift (Spec.map (CommRingCat.ofHom φ) ≫ a)
    (Spec.map (CommRingCat.ofHom (algebraMap k K))) hw
  let r : X ⟶ pullback f (absoluteFrobeniusPow (Spec (.of k)) p
      (isInCharacteristic_spec k p) n) :=
    (nFoldRelativeFrobenius (Spec (.of k)) p (isInCharacteristic_spec k p) n (Over.mk f)).left
  have hb₁ : b ≫ pullback.fst f (absoluteFrobeniusPow (Spec (.of k)) p
      (isInCharacteristic_spec k p) n) = Spec.map (CommRingCat.ofHom φ) ≫ a :=
    pullback.lift_fst _ _ _
  have hb₂ : b ≫ pullback.snd f (absoluteFrobeniusPow (Spec (.of k)) p
      (isInCharacteristic_spec k p) n) =
      Spec.map (CommRingCat.ofHom (algebraMap k K)) := pullback.lift_snd _ _ _
  have hr₁ : r ≫ pullback.fst f (absoluteFrobeniusPow (Spec (.of k)) p
      (isInCharacteristic_spec k p) n) =
      absoluteFrobeniusPow X p (isInCharacteristic_of_hom f p (isInCharacteristic_spec k p)) n :=
    nFoldRelativeFrobenius_fst _ _ _ _ _
  have hr₂ : r ≫ pullback.snd f (absoluteFrobeniusPow (Spec (.of k)) p
      (isInCharacteristic_spec k p) n) = f := nFoldRelativeFrobenius_snd _ _ _ _ _
  refine ⟨n, b, hb₂, ?_⟩
  change Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ b = a ≫ r
  apply pullback.hom_ext
  · rw [Category.assoc, hb₁, ← Category.assoc, ← Spec.map_comp, Category.assoc, hr₁]
    have hp : CommRingCat.ofHom φ ≫ CommRingCat.ofHom (algebraMap K L) =
        CommRingCat.ofHom (_root_.iterateFrobenius L p n) := by
      ext z
      exact (hφ z).trans (iterateFrobenius_def p n z).symm
    rw [hp, ← absoluteFrobeniusPow_spec]
    exact absoluteFrobeniusPow_comp_natural a p (isInCharacteristic_spec L p) _ n
  · rw [Category.assoc, hb₂, Category.assoc, hr₂, ha, ← Spec.map_comp]
    congr 2

/-- An actual closed point has separable residue field after finitely many actual relative
Frobenius iterations. The target point is the image under the native iterated map. -/
@[colib_tag "COL-1106", colib_ref "axiom_stacks_5ed82d14"
  "StacksFrontier/AlgebraicGeometry/Variety/Curve/RamificationAlgebraicClosure.lean:234-255"
  "ingredient"
  "Original closed residue finiteness; the separable-image Frobenius assembly is proved here."]
theorem exists_isClosed_isSeparable_nFoldRelativeFrobenius_image
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [IsSeparated f]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ n : ℕ,
      let T := nFoldFrobeniusTwist (Spec (.of k)) p (isInCharacteristic_spec k p) n (Over.mk f)
      let y := (nFoldRelativeFrobenius (Spec (.of k)) p
        (isInCharacteristic_spec k p) n (Over.mk f)).left x
      IsClosed ({y} : Set T.left) ∧
        letI := (fieldToResidue T.hom y).hom.toAlgebra
        Algebra.IsSeparable k (T.left.residueField y) := by
  let L := X.residueField x
  let : Algebra k L := (fieldToResidue f x).hom.toAlgebra
  have : Module.Finite k L := finite_residueField_overField_of_isClosed f x hx
  obtain ⟨n, b, hb, hmark⟩ := exists_separableFieldPoint_nFoldRelativeFrobenius
    (k := k) (L := L) p f (X.fromSpecResidueField x)
    (Scheme.fromSpecResidueField_comp_eq_spec_fieldToResidue f x)
  let K := separableClosure k L
  let T := nFoldFrobeniusTwist (Spec (.of k)) p (isInCharacteristic_spec k p) n (Over.mk f)
  let y := (nFoldRelativeFrobenius (Spec (.of k)) p
    (isInCharacteristic_spec k p) n (Over.mk f)).left x
  have hy : b (IsLocalRing.closedPoint K) = y := by
    let z : Spec (.of L) := IsLocalRing.closedPoint L
    let r : X ⟶ T.left := (nFoldRelativeFrobenius (Spec (.of k)) p
      (isInCharacteristic_spec k p) n (Over.mk f)).left
    have h := congrArg (fun a : Spec (.of L) ⟶ T.left => a z) hmark
    calc
      b (IsLocalRing.closedPoint K) =
          b (Spec.map (CommRingCat.ofHom (algebraMap K L)) z) :=
        congrArg b (Subsingleton.elim _ _)
      _ = r (X.fromSpecResidueField x z) := h
      _ = y := congrArg r (X.fromSpecResidueField_apply x z)
  have : IsSeparated T.hom :=
    inferInstanceAs (IsSeparated (pullback.snd f
      (absoluteFrobeniusPow (Spec (.of k)) p (isInCharacteristic_spec k p) n)))
  refine ⟨n, ?_⟩
  change IsClosed ({y} : Set T.left) ∧
    letI := (fieldToResidue T.hom y).hom.toAlgebra
    Algebra.IsSeparable k (T.left.residueField y)
  rw [← hy]
  exact ⟨isClosed_image_of_finite_fieldPoint T.hom b hb,
    isSeparable_residueField_of_fieldPoint T.hom b hb⟩

end AlgebraicGeometry
