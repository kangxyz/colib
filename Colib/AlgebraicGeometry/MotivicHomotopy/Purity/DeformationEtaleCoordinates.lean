/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.CoordinateFibreMaps
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.DeformationPairMaps
public import Colib.AlgebraicGeometry.Sites.Smooth.Cohomology.GenericOpen

/-!
# Affine étale coordinates for smooth closed pairs

An affine étale chart for a smooth closed pair identifies its original
centre with the zero coordinate subspace.
-/

public noncomputable section

set_option quotPrecheck false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.Scheme.SmoothSite.Contraction
open AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
open Stacks.Deformation Stacks.MoreMorphisms

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k]

local notation "Sm(" field ")" => SmoothSite (Spec (CommRingCat.of field))

variable (m n : ℕ)

/-- The literal coordinate immersion as a morphism over the coefficient field. -/
abbrev coordinatePairImmersion :
    affineSite k (MvPolynomial (Fin m) k) ⟶ affineSite k (MvPolynomial (Fin m ⊕ Fin n) k) :=
  affineMorphism (coordinateProjectionAlgHom k m n)

local notation "i₀" => coordinatePairImmersion k m n

private def coordinateModelBaseIso (σ : Type) :
    Spec (CommRingCat.of (MvPolynomial σ Γ(Spec (.of k), ⊤))) ≅
      Spec (CommRingCat.of (MvPolynomial σ k)) :=
  Scheme.Spec.mapIso
    ((MvPolynomial.mapEquiv σ
      (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv).toCommRingCatIso.op.symm)

private theorem coordinateModelBaseIso_over (σ : Type) [Finite σ] :
    (coordinateModelBaseIso k σ).hom ≫ (affineSite k (MvPolynomial σ k)).hom =
      Spec.map (CommRingCat.ofHom (MvPolynomial.C :
        Γ(Spec (.of k), ⊤) →+* MvPolynomial σ Γ(Spec (.of k), ⊤))) ≫
        (Spec (.of k)).isoSpec.inv := by
  change Spec.map (CommRingCat.ofHom
      (MvPolynomial.map (σ := σ) (Scheme.ΓSpecIso (.of k)).inv.hom)) ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial σ k)) = _
  rw [Scheme.isoSpec_Spec_inv, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact MvPolynomial.map_C _ _

private theorem coordinateModelBaseIso_immersion :
    coordinateEmbedding Γ(Spec (.of k), ⊤) m n ≫
        (coordinateModelBaseIso k (Fin m ⊕ Fin n)).hom =
      (coordinateModelBaseIso k (Fin m)).hom ≫ (i₀).left := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [coordinateProjection]
  · intro x
    cases x <;> simp [coordinateProjection, coordinateProjectionAlgHom]

/-- An affine open coordinate chart around any point of the original closed centre. -/
theorem exists_affine_open_etale_coordinates
    {Z X : Sm(k)} (i : Z ⟶ X) [IsClosedImmersion i.left] (z : Z.left) :
    ∃ (U : X.left.Opens) (_ : IsAffineOpen U) (_ : i.left z ∈ U) (m n : ℕ)
      (a : (opensFunctor X).obj U ⟶ affineSite k (MvPolynomial (Fin m ⊕ Fin n) k))
      (b : (opensFunctor Z).obj (i.left ⁻¹ᵁ U) ⟶ affineSite k (MvPolynomial (Fin m) k)),
      Etale a.left ∧ IsPullback
        (i.left.resLE U (i.left ⁻¹ᵁ U) le_rfl) b.left a.left
          (coordinatePairImmersion k m n).left := by
  let S := Spec (CommRingCat.of k)
  let : Smooth (i.left ≫ X.hom) := smooth_closedPair_comp i
  obtain ⟨m, n, V, hzV, f, g, hf, hover, hpb⟩ :=
    Stacks.AlgebraicGeometry.exists_etale_coordinateSubspaceEmbedding_isPullback X.hom i.left z
  obtain ⟨U, hU, hzU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (show i.left z ∈ V from hzV)
  let u := X.left.homOfLE hUV
  let v := Z.left.homOfLE (i.left.preimage_mono hUV)
  let ex := Stacks.Deformation.affineSpaceIsoSpecRename S
    (Equiv.ulift.{u}.trans finSumFinEquiv.symm : ULift.{u} (Fin (m + n)) ≃ Fin m ⊕ Fin n)
  let ez := Stacks.Deformation.affineSpaceIsoSpecRename S (Equiv.ulift.{u} (α := Fin m))
  let f₀ := f ≫ ex.hom ≫ (coordinateModelBaseIso k (Fin m ⊕ Fin n)).hom
  let g₀ := g ≫ ez.hom ≫ (coordinateModelBaseIso k (Fin m)).hom
  have hmodel := Stacks.Deformation.isPullback_coordinateSubspaceEmbedding_coordinateEmbedding S m n
  have hbase : IsPullback (coordinateModelBaseIso k (Fin m)).hom
      (coordinateEmbedding Γ(S, ⊤) m n) (coordinatePairImmersion k m n).left
      (coordinateModelBaseIso k (Fin m ⊕ Fin n)).hom := by
    apply IsPullback.of_horiz_isIso
    exact ⟨(coordinateModelBaseIso_immersion k m n).symm⟩
  have H := ((hpb.flip.paste_horiz hmodel).paste_horiz hbase).flip
  have hu : IsPullback (i.left.resLE U (i.left ⁻¹ᵁ U) le_rfl) v u
      (i.left.resLE V (i.left ⁻¹ᵁ V) le_rfl) := by
    have h₁ : IsPullback (i.left.resLE U (i.left ⁻¹ᵁ U) le_rfl)
        (i.left ⁻¹ᵁ U).ι U.ι i.left := by
      rw [Scheme.Hom.resLE_eq_morphismRestrict]
      exact isPullback_morphismRestrict i.left U
    have h₂ : IsPullback (i.left.resLE V (i.left ⁻¹ᵁ V) le_rfl)
        (i.left ⁻¹ᵁ V).ι V.ι i.left := by
      rw [Scheme.Hom.resLE_eq_morphismRestrict]
      exact isPullback_morphismRestrict i.left V
    have h₃ : IsPullback (i.left.resLE U (i.left ⁻¹ᵁ U) le_rfl)
        (v ≫ (i.left ⁻¹ᵁ V).ι) (u ≫ V.ι) i.left := by
      rw [show v ≫ (i.left ⁻¹ᵁ V).ι = (i.left ⁻¹ᵁ U).ι from Scheme.homOfLE_ι _ _]
      rw [show u ≫ V.ι = U.ι from Scheme.homOfLE_ι _ _]
      exact h₁
    apply h₃.of_bot _ h₂
    apply (cancel_mono V.ι).1
    have hau : u ≫ V.ι = U.ι := Scheme.homOfLE_ι _ _
    have hbv : v ≫ (i.left ⁻¹ᵁ V).ι = (i.left ⁻¹ᵁ U).ι := Scheme.homOfLE_ι _ _
    calc
      _ = i.left.resLE U (i.left ⁻¹ᵁ U) le_rfl ≫ U.ι :=
        (Category.assoc _ _ _).trans (congrArg (i.left.resLE U _ le_rfl ≫ ·) hau)
      _ = (i.left ⁻¹ᵁ U).ι ≫ i.left := h₁.w
      _ = (v ≫ (i.left ⁻¹ᵁ V).ι) ≫ i.left := (congrArg (· ≫ i.left) hbv).symm
      _ = _ := (Category.assoc _ _ _).trans
        ((congrArg (v ≫ ·) h₂.w.symm).trans (Category.assoc _ _ _).symm)
  have hpbU : IsPullback (i.left.resLE U (i.left ⁻¹ᵁ U) le_rfl)
      (v ≫ g₀) (u ≫ f₀) (coordinatePairImmersion k m n).left := by
    simpa only [f₀, g₀, Category.assoc] using hu.paste_vert H
  have hf₀ : f₀ ≫ (affineSite k (MvPolynomial (Fin m ⊕ Fin n) k)).hom = V.ι ≫ X.hom := by
    have he : ex.hom ≫ Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : Γ(S, ⊤) →+* MvPolynomial (Fin m ⊕ Fin n) Γ(S, ⊤))) =
        (AffineSpace.over (ULift.{u} (Fin (m + n))) S).hom ≫ S.isoSpec.hom :=
      Stacks.Deformation.affineSpaceIsoSpecRename_hom_comp S m n
    simp only [f₀, Category.assoc, coordinateModelBaseIso_over]
    rw [← Category.assoc ex.hom, he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact hover
  let A : (opensFunctor X).obj U ⟶ affineSite k (MvPolynomial (Fin m ⊕ Fin n) k) :=
    homMk (u ≫ f₀) (by
      change (u ≫ f₀) ≫ _ = U.ι ≫ X.hom
      rw [Category.assoc, hf₀]
      simp only [u, Scheme.homOfLE_ι_assoc])
  let B : (opensFunctor Z).obj (i.left ⁻¹ᵁ U) ⟶ affineSite k (MvPolynomial (Fin m) k) :=
    homMk (v ≫ g₀) (by
      change (v ≫ g₀) ≫ (affineSite k (MvPolynomial (Fin m) k)).hom = _
      rw [← MorphismProperty.Over.w (coordinatePairImmersion k m n), ← Category.assoc,
        ← hpbU.w, Category.assoc]
      have hA : (u ≫ f₀) ≫ (affineSite k (MvPolynomial (Fin m ⊕ Fin n) k)).hom =
          U.ι ≫ X.hom := MorphismProperty.Over.w A
      rw [hA, ← Category.assoc,
        Scheme.Hom.resLE_comp_ι, Category.assoc, MorphismProperty.Over.w i]
      rfl)
  let : Etale f := hf
  exact ⟨U, hU, hzU, m, n, A, B, inferInstanceAs (Etale (u ≫ f₀)), hpbU⟩

end AlgebraicGeometry.MotivicHomotopy
