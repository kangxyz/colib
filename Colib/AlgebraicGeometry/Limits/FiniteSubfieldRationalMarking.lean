/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Morphisms.FiniteType.FiniteSubfieldPoint
public import Colib.RingTheory.TensorProduct.FiniteSubfieldModels
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Rational tensor markings on actual finite-subfield stages

A point already defined over an actual finite subfield gives a rational point of every
larger tensor stage. The native affine pullback constructs that point as a section of the
stage structure map. Its original geometric marking factors through that section, and its
underlying point is exactly the image under the original tensor inclusion. Closedness of a
point or existence of a geometric marking is never substituted for rationality.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits IntermediateField

universe u

namespace AlgebraicGeometry.Scheme

/-- The native affine pullback turns an actual field-valued point into a rational tensor point. -/
def rationalTensorPoint (K E B : Type u) [Field K] [Field E] [Algebra K E]
    [CommRing B] [Algebra K B] (ξ : Spec (.of E) ⟶ Spec (.of B))
    (hξ : ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) =
      Spec.map (CommRingCat.ofHom (algebraMap K E))) :
    Spec (.of E) ⟶ Spec (.of (E ⊗[K] B)) :=
  pullback.lift (𝟙 _) ξ (by simpa using hξ.symm) ≫ (pullbackSpecIso K E B).hom

/-- The tensor point is a section over the actual stage field, not just a geometric point. -/
@[simp, reassoc]
theorem rationalTensorPoint_fst (K E B : Type u) [Field K] [Field E] [Algebra K E]
    [CommRing B] [Algebra K B] (ξ : Spec (.of E) ⟶ Spec (.of B))
    (hξ : ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) =
      Spec.map (CommRingCat.ofHom (algebraMap K E))) :
    rationalTensorPoint K E B ξ hξ ≫
      Spec.map (CommRingCat.ofHom (algebraMap E (E ⊗[K] B))) = 𝟙 _ := by
  simp [rationalTensorPoint]

/-- The other projection retains the original field-valued point. -/
@[reassoc]
theorem rationalTensorPoint_snd (K E B : Type u) [Field K] [Field E] [Algebra K E]
    [CommRing B] [Algebra K B] (ξ : Spec (.of E) ⟶ Spec (.of B))
    (hξ : ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) =
      Spec.map (CommRingCat.ofHom (algebraMap K E))) :
    rationalTensorPoint K E B ξ hξ ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := K) (A := E) (B := B)).toRingHom) = ξ := by
  simp [rationalTensorPoint]

/-- Both projections determine maps to the native affine tensor scheme. -/
theorem tensorSpec_hom_ext (K E B : Type u) [Field K] [Field E] [Algebra K E]
    [CommRing B] [Algebra K B] {Y : Scheme.{u}}
    {f g : Y ⟶ Spec (.of (E ⊗[K] B))}
    (hfst : f ≫ Spec.map (CommRingCat.ofHom (algebraMap E (E ⊗[K] B))) =
      g ≫ Spec.map (CommRingCat.ofHom (algebraMap E (E ⊗[K] B))))
    (hsnd : f ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := K) (A := E) (B := B)).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := K) (A := E) (B := B)).toRingHom)) : f = g := by
  rw [← cancel_mono (pullbackSpecIso K E B).inv]
  apply pullback.hom_ext
  · simpa only [Category.assoc, pullbackSpecIso_inv_fst'] using hfst
  · simpa only [Category.assoc, pullbackSpecIso_inv_snd, AlgHom.toRingHom_eq_coe] using hsnd

/-- Scalar extension preserves the actual first projection. -/
@[reassoc]
theorem tensorSpec_map_fst (K E L B : Type u) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [CommRing B] [Algebra K B] (φ : E →ₐ[K] L) :
    Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map φ (AlgHom.id K B)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap E (E ⊗[K] B))) =
    Spec.map (CommRingCat.ofHom (algebraMap L (L ⊗[K] B))) ≫
      Spec.map (CommRingCat.ofHom φ.toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  congr 1

/-- Scalar extension preserves the actual second projection. -/
@[reassoc]
theorem tensorSpec_map_snd (K E L B : Type u) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [CommRing B] [Algebra K B] (φ : E →ₐ[K] L) :
    Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map φ (AlgHom.id K B)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := K) (A := E) (B := B)).toRingHom) =
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := B)).toRingHom) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  ext x
  simp

/-- Any compatible original marking factors through the rational tensor point after scalar
extension. The source can be a further geometric-point field or any other scheme. -/
theorem rationalTensorPoint_marking (K E L B : Type u) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [CommRing B] [Algebra K B] (φ : E →ₐ[K] L)
    (ξ : Spec (.of E) ⟶ Spec (.of B))
    (hξ : ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) =
      Spec.map (CommRingCat.ofHom (algebraMap K E)))
    {Y : Scheme.{u}} (η : Y ⟶ Spec (.of L)) (x : Y ⟶ Spec (.of (L ⊗[K] B)))
    (hx₁ : x ≫ Spec.map (CommRingCat.ofHom (algebraMap L (L ⊗[K] B))) = η)
    (hx₂ : x ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := B)).toRingHom) =
      η ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ξ) :
    η ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ rationalTensorPoint K E B ξ hξ =
      x ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map φ (AlgHom.id K B)).toRingHom) := by
  apply tensorSpec_hom_ext K E B
  · simp only [Category.assoc, rationalTensorPoint_fst, Category.comp_id, tensorSpec_map_fst]
    rw [← Category.assoc, hx₁]
  · simpa only [Category.assoc, rationalTensorPoint_snd, tensorSpec_map_snd] using hx₂.symm

/-- A point at one actual finite subfield is rational on every larger tensor stage, with
its exact geometric marking and the producer's tensor-comap point unchanged. -/
theorem exists_rationalTensorMarking_of_finsetSubset
    (K L B : Type u) [Field K] [Field L] [Algebra K L] [CommRing B] [Algebra K B]
    {s t : Finset L} (hst : s ⊆ t)
    (ξ : Spec (.of (adjoin K (s : Set L))) ⟶ Spec (.of B))
    (hξ : ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) =
      Spec.map (CommRingCat.ofHom (algebraMap K (adjoin K (s : Set L)))))
    {Y : Scheme.{u}} (η : Y ⟶ Spec (.of L)) (x : Y ⟶ Spec (.of (L ⊗[K] B)))
    (hx₁ : x ≫ Spec.map (CommRingCat.ofHom (algebraMap L (L ⊗[K] B))) = η)
    (hx₂ : x ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := B)).toRingHom) =
      η ≫ Spec.map (CommRingCat.ofHom (adjoin K (s : Set L)).val.toRingHom) ≫ ξ) :
    ∃ xE : Spec (.of (adjoin K (t : Set L))) ⟶
        Spec (.of ((adjoin K (t : Set L)) ⊗[K] B)),
      xE ≫ Spec.map (CommRingCat.ofHom
        (algebraMap (adjoin K (t : Set L)) ((adjoin K (t : Set L)) ⊗[K] B))) = 𝟙 _ ∧
      η ≫ Spec.map (CommRingCat.ofHom (adjoin K (t : Set L)).val.toRingHom) ≫ xE =
        x ≫ Spec.map (CommRingCat.ofHom (finsetTensorInclusion K L B t).toRingHom) ∧
      ∀ y : Y, xE default =
        Spec.map (CommRingCat.ofHom (finsetTensorInclusion K L B t).toRingHom) (x y) := by
  let φ := inclusion (adjoin.mono K _ _ (Finset.coe_subset.mpr hst))
  let ξt := Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ξ
  have hξt : ξt ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) =
      Spec.map (CommRingCat.ofHom (algebraMap K (adjoin K (t : Set L)))) := by
    dsimp only [ξt]
    rw [Category.assoc, hξ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
  have hval : Spec.map (CommRingCat.ofHom (adjoin K (t : Set L)).val.toRingHom) ≫
      Spec.map (CommRingCat.ofHom φ.toRingHom) =
      Spec.map (CommRingCat.ofHom (adjoin K (s : Set L)).val.toRingHom) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hmark := rationalTensorPoint_marking K (adjoin K (t : Set L)) L B
    (adjoin K (t : Set L)).val ξt hξt η x hx₁ (by
      dsimp only [ξt]
      rw [← Category.assoc (Spec.map _) (Spec.map _) ξ, hval]
      exact hx₂)
  refine ⟨rationalTensorPoint K (adjoin K (t : Set L)) B ξt hξt,
    rationalTensorPoint_fst K (adjoin K (t : Set L)) B ξt hξt, hmark, ?_⟩
  intro y
  have h := congrArg (fun f : Y ⟶ Spec (.of ((adjoin K (t : Set L)) ⊗[K] B)) => f y) hmark
  simpa only [Scheme.Hom.comp_apply, finsetTensorInclusion, Subsingleton.elim
    (Spec.map (CommRingCat.ofHom (adjoin K (t : Set L)).val.toRingHom) (η y)) default] using h

/-- The actual finite-subfield point producer supplies rational markings at all later stages.
A further geometric-point source retains its original marking through the actual tensor map. -/
theorem exists_finsetSubfield_rationalTensorMarking
    (K L B : Type u) [Field K] [Field L] [Algebra K L] [CommRing B] [Algebra K B]
    [Algebra.FiniteType K B] (ξ : Spec (.of L) ⟶ Spec (.of B))
    (hξ : ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) =
      Spec.map (CommRingCat.ofHom (algebraMap K L)))
    {Y : Scheme.{u}} (η : Y ⟶ Spec (.of L)) (x : Y ⟶ Spec (.of (L ⊗[K] B)))
    (hx₁ : x ≫ Spec.map (CommRingCat.ofHom (algebraMap L (L ⊗[K] B))) = η)
    (hx₂ : x ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := B)).toRingHom) = η ≫ ξ)
    (s : Finset L) :
    ∃ s₀ : Finset L, s ⊆ s₀ ∧ ∀ (t : Finset L), s₀ ⊆ t →
      ∃ xE : Spec (.of (adjoin K (t : Set L))) ⟶
          Spec (.of ((adjoin K (t : Set L)) ⊗[K] B)),
        xE ≫ Spec.map (CommRingCat.ofHom
          (algebraMap (adjoin K (t : Set L)) ((adjoin K (t : Set L)) ⊗[K] B))) = 𝟙 _ ∧
        η ≫ Spec.map (CommRingCat.ofHom (adjoin K (t : Set L)).val.toRingHom) ≫ xE =
          x ≫ Spec.map (CommRingCat.ofHom (finsetTensorInclusion K L B t).toRingHom) ∧
        ∀ y : Y, xE default =
          Spec.map (CommRingCat.ofHom (finsetTensorInclusion K L B t).toRingHom) (x y) := by
  obtain ⟨s₀, hs₀, ξ₀, hξ₀, hmark⟩ := exists_point_finsetSubfield K L B ξ hξ s
  refine ⟨s₀, hs₀, fun t ht =>
    exists_rationalTensorMarking_of_finsetSubset K L B ht ξ₀ hξ₀ η x hx₁ ?_⟩
  rw [hmark]
  exact hx₂

end AlgebraicGeometry.Scheme
