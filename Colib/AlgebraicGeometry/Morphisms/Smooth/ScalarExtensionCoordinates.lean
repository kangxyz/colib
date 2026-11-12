/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.MvPolynomial.ScalarExtensionPushout
public import Colib.AlgebraicGeometry.Morphisms.Smooth.RelativeDimensionDescent
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Relative dimension of the original scalar-extended coordinates

The actual localized coordinate square is cartesian. Surjectivity of the field coefficient
base change and native smooth descent give the same smooth relative dimension on the original
principal open, including the actual intermediate-field tensor model.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits MvPolynomial

universe u

namespace AlgebraicGeometry
open CommRingCat
variable (E L B : Type u) [Field E] [Field L] [Algebra E L]
 [CommRing B] [Algebra E B] {ι : Type} (g : ι → B)
/-- The original principal-open coordinate map has its actual scalar-extension pullback square. -/
theorem isPullback_aevalAway_scalarExtension (r : B) :
    IsPullback
      (Spec.map (ofHom (IsLocalization.Away.mapₐ (Localization.Away r)
        (Localization.Away ((Algebra.TensorProduct.includeRight : B →ₐ[E] L ⊗[E] B) r))
        (Algebra.TensorProduct.includeRight : B →ₐ[E] L ⊗[E] B) r).toRingHom))
      (Spec.map (ofHom ((algebraMap (L ⊗[E] B)
        (Localization.Away ((1 : L) ⊗ₜ[E] r))).comp
        (aeval (R := L) (fun i => (1 : L) ⊗ₜ[E] g i)).toRingHom)))
      (Spec.map (ofHom ((algebraMap B (Localization.Away r)).comp
        (aeval (R := E) g).toRingHom)))
      (Spec.map (ofHom (MvPolynomial.map (algebraMap E L) :
        MvPolynomial ι E →+* MvPolynomial ι L))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _
    (MvPolynomial.isPushout_aevalAway_scalarExtension E L B g r)

omit B [CommRing B] [Algebra E B] g in
/-- A field extension is surjective on the spectra of the actual polynomial coordinate rings. -/
theorem surjective_SpecMap_mvPolynomial_fieldExtension :
    Surjective (Spec.map (ofHom (MvPolynomial.map (algebraMap E L) :
      MvPolynomial ι E →+* MvPolynomial ι L))) := by
  let := MvPolynomial.algebraMvPolynomial (R := E) (S := L) (σ := ι)
  have h := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout E L (MvPolynomial ι E) (MvPolynomial ι L))
  have : Surjective (Spec.map (ofHom (algebraMap E L))) :=
    ⟨Function.surjective_to_subsingleton _⟩
  exact MorphismProperty.of_isPullback h inferInstance

/-- Smooth relative dimension descends on the original principal-open coordinate map. -/
theorem smoothOfRelativeDimension_aevalAway_of_scalarExtension (r : B) (n : ℕ)
    [hrel : SmoothOfRelativeDimension n (Spec.map (ofHom
      ((algebraMap (L ⊗[E] B) (Localization.Away ((1 : L) ⊗ₜ[E] r))).comp
        (aeval (R := L) (fun i => (1 : L) ⊗ₜ[E] g i)).toRingHom)))] :
    SmoothOfRelativeDimension n (Spec.map (ofHom
      ((algebraMap B (Localization.Away r)).comp (aeval (R := E) g).toRingHom))) := by
  have hs : ((algebraMap (L ⊗[E] B) (Localization.Away ((1 : L) ⊗ₜ[E] r))).comp
      (aeval (R := L) (fun i => (1 : L) ⊗ₜ[E] g i)).toRingHom).Smooth :=
    (HasRingHomProperty.Spec_iff (P := @Smooth) (φ := ofHom
      ((algebraMap (L ⊗[E] B) (Localization.Away ((1 : L) ⊗ₜ[E] r))).comp
        (aeval (R := L) (fun i => (1 : L) ⊗ₜ[E] g i)).toRingHom))).mp
      (SmoothOfRelativeDimension.smooth n _)
  have : Smooth (Spec.map (ofHom
      ((algebraMap B (Localization.Away r)).comp (aeval (R := E) g).toRingHom))) :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
      (MvPolynomial.of_aevalAway_scalarExtension E L B g _
        RingHom.Smooth.codescendsAlong_faithfullyFlat RingHom.Smooth.respectsIso r hs)
  have := surjective_SpecMap_mvPolynomial_fieldExtension E L (ι := ι)
  exact @SmoothOfRelativeDimension.of_surjective_isPullback _ _ _ _ _ _ _ _
    (isPullback_aevalAway_scalarExtension E L B g r) inferInstance inferInstance n hrel
end AlgebraicGeometry

namespace AlgebraicGeometry
open CommRingCat
variable (K E L B : Type u) [Field K] [Field E] [Field L]
 [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
 [CommRing B] [Algebra K B] {ι : Type} (g : ι → E ⊗[K] B)
/-- The actual intermediate-field principal-open map is the original coordinate base change. -/
theorem isPullback_aevalAway_scalarTower (r : E ⊗[K] B) :
    IsPullback
      (Spec.map (ofHom (IsLocalization.Away.mapₐ (Localization.Away r)
        (Localization.Away
          (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) r))
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K E L) (AlgHom.id K B)) r).toRingHom))
      (Spec.map (ofHom ((algebraMap (L ⊗[K] B)
        (Localization.Away
          (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) r))).comp
        (aeval (R := L) (fun i => Algebra.TensorProduct.map
          (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) (g i))).toRingHom)))
      (Spec.map (ofHom ((algebraMap (E ⊗[K] B) (Localization.Away r)).comp
        (aeval (R := E) g).toRingHom)))
      (Spec.map (ofHom (MvPolynomial.map (algebraMap E L) :
        MvPolynomial ι E →+* MvPolynomial ι L))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _
    (MvPolynomial.isPushout_aevalAway_scalarTower K E L B g r)

/-- Smooth relative dimension descends to the actual intermediate-field principal-open model. -/
theorem smoothOfRelativeDimension_aevalAway_of_scalarTower (r : E ⊗[K] B) (n : ℕ)
    [hrel : SmoothOfRelativeDimension n (Spec.map (ofHom
      ((algebraMap (L ⊗[K] B) (Localization.Away
          (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) r))).comp
        (aeval (R := L) (fun i => Algebra.TensorProduct.map
          (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) (g i))).toRingHom)))] :
    SmoothOfRelativeDimension n (Spec.map (ofHom
      ((algebraMap (E ⊗[K] B) (Localization.Away r)).comp (aeval (R := E) g).toRingHom))) := by
  have hs : ((algebraMap (L ⊗[K] B) (Localization.Away
          (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) r))).comp
      (aeval (R := L) (fun i => Algebra.TensorProduct.map
          (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) (g i))).toRingHom).Smooth :=
    (HasRingHomProperty.Spec_iff (P := @Smooth) (φ := ofHom
      ((algebraMap (L ⊗[K] B) (Localization.Away
          (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) r))).comp
        (aeval (R := L) (fun i => Algebra.TensorProduct.map
          (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) (g i))).toRingHom))).mp
      (SmoothOfRelativeDimension.smooth n _)
  have : Smooth (Spec.map (ofHom
      ((algebraMap (E ⊗[K] B) (Localization.Away r)).comp (aeval (R := E) g).toRingHom))) :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
      (MvPolynomial.of_aevalAway_scalarTower K E L B g _
        RingHom.Smooth.codescendsAlong_faithfullyFlat RingHom.Smooth.respectsIso r hs)
  have := surjective_SpecMap_mvPolynomial_fieldExtension E L (ι := ι)
  exact @SmoothOfRelativeDimension.of_surjective_isPullback _ _ _ _ _ _ _ _
    (isPullback_aevalAway_scalarTower K E L B g r) inferInstance inferInstance n hrel
end AlgebraicGeometry

namespace AlgebraicGeometry
/-- The native principal-open spectrum comparison retains smooth relative dimension. -/
theorem smoothOfRelativeDimension_basicOpen_iff
    (A B : Type u) [CommRing A] [CommRing B] (f : A →+* B) (r : B) (n : ℕ) :
    SmoothOfRelativeDimension n
      ((Scheme.Opens.ι (X := Spec (.of B)) (PrimeSpectrum.basicOpen r)) ≫
        Spec.map (CommRingCat.ofHom f)) ↔
    SmoothOfRelativeDimension n
      (Spec.map (CommRingCat.ofHom ((algebraMap B (Localization.Away r)).comp f))) := by
  have h : (basicOpenIsoSpecAway (R := .of B) r).hom ≫
      Spec.map (CommRingCat.ofHom ((algebraMap B (Localization.Away r)).comp f)) =
      (Scheme.Opens.ι (X := Spec (.of B)) (PrimeSpectrum.basicOpen r)) ≫
        Spec.map (CommRingCat.ofHom f) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, ← Category.assoc,
      basicOpenIsoSpecAway_hom_SpecMap]
  let : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{u} n) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension.{u} n)
      (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n))
  rw [← h]
  constructor
  · intro hf
    have h' := IsZariskiLocalAtSource.comp hf (basicOpenIsoSpecAway (R := .of B) r).inv
    simpa only [Iso.inv_hom_id_assoc] using h'
  · intro hf
    exact IsZariskiLocalAtSource.comp hf (basicOpenIsoSpecAway (R := .of B) r).hom
end AlgebraicGeometry
open scoped TensorProduct
namespace AlgebraicGeometry
open MvPolynomial CommRingCat
variable (K E L B : Type u) [Field K] [Field E] [Field L]
  [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
  [CommRing B] [Algebra K B] {ι : Type} (g : ι → E ⊗[K] B)
/-- Relative dimension descends on the original principal open as a scheme open. -/
theorem smoothOfRelativeDimension_basicOpen_of_scalarTower
    (r : E ⊗[K] B) (n : ℕ)
    (hrel : SmoothOfRelativeDimension n
      ((Scheme.Opens.ι (X := Spec (.of (L ⊗[K] B))) (PrimeSpectrum.basicOpen
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) r))) ≫
        Spec.map (ofHom (aeval (R := L) (fun i => Algebra.TensorProduct.map
          (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) (g i))).toRingHom))) :
    SmoothOfRelativeDimension n
      ((Scheme.Opens.ι (X := Spec (.of (E ⊗[K] B))) (PrimeSpectrum.basicOpen r)) ≫
        Spec.map (ofHom (aeval (R := E) g).toRingHom)) := by
  apply (smoothOfRelativeDimension_basicOpen_iff _ _ _ r n).mpr
  have h := (smoothOfRelativeDimension_basicOpen_iff _ _ _ _ n).mp hrel
  exact smoothOfRelativeDimension_aevalAway_of_scalarTower K E L B g r n (hrel := h)
end AlgebraicGeometry
