/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Sections of the actual pullback of an affine scheme over a spectrum

The tensor algebra identifies the global sections of the chosen scheme
pullback. Its coefficient map is pullback along the actual second
projection, read through the canonical sections of a spectrum.

The comparison adapts the section isomorphism in
`Motivic/Aglib/AlgebraicGeometry/Normalization/FiniteCurve/PolynomialChartFiniteFlat.lean`
at a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme

/-- The canonical sections comparison of an actual affine Cartesian square. -/
def affineSectionsComparisonOfIsPullback {S X Y P : Scheme.{u}}
    [IsAffine S] [IsAffine X] [IsAffine Y] {f : X ⟶ S} {g : Y ⟶ S}
    {a : P ⟶ X} {b : P ⟶ Y} (h : IsPullback a b f g) :
    letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    letI : Algebra Γ(S, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
    letI : Algebra Γ(Y, ⊤) Γ(P, ⊤) := b.appTop.hom.toAlgebra
    {e : Γ(Y, ⊤) ⊗[Γ(S, ⊤)] Γ(X, ⊤) ≃ₐ[Γ(Y, ⊤)] Γ(P, ⊤) //
      ∀ s : Γ(X, ⊤), e ((1 : Γ(Y, ⊤)) ⊗ₜ[Γ(S, ⊤)] s) = a.appTop s} := by
  letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  letI : Algebra Γ(S, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
  letI : Algebra Γ(Y, ⊤) Γ(P, ⊤) := b.appTop.hom.toAlgebra
  let H := CommRingCat.isPushout_tensorProduct Γ(S, ⊤) Γ(Y, ⊤) Γ(X, ⊤)
  let K := (isPushout_appTop_of_isPullback h).flip
  let e := H.isoIsPushout _ _ K
  have h₁ := IsPushout.inl_isoIsPushout_hom _ _ H K
  have h₂ := IsPushout.inr_isoIsPushout_hom _ _ H K
  refine ⟨{ e.commRingCatIsoToRingEquiv with commutes' := fun a ↦ ?_ }, fun s ↦ ?_⟩
  · exact congrArg (fun k : Γ(Y, ⊤) ⟶ Γ(P, ⊤) ↦ k.hom a) h₁
  · exact congrArg (fun k : Γ(X, ⊤) ⟶ Γ(P, ⊤) ↦ k.hom s) h₂

/-- The actual chosen pullback comparison retains the pullback of the original
sections along its first projection. -/
abbrev affinePullbackSectionsComparison {S X Y : Scheme.{u}}
    [IsAffine S] [IsAffine X] [IsAffine Y] (f : X ⟶ S) (g : Y ⟶ S) :=
  affineSectionsComparisonOfIsPullback (IsPullback.of_hasPullback f g)

/-- The actual coefficient action on global sections of a scheme over a spectrum. -/
abbrev specSectionsMap {A : Type u} [CommRing A] {X : Scheme.{u}}
    (q : X ⟶ Spec (.of A)) : A →+* Γ(X, ⊤) :=
  ((ΓSpecIso (.of A)).inv ≫ q.appTop).hom

/-- The section map presents the original morphism with the canonical affine coordinates. -/
theorem Spec_map_specSectionsMap {A : Type u} [CommRing A]
    {X : Scheme.{u}} [IsAffine X] (q : X ⟶ Spec (.of A)) :
    Spec.map (CommRingCat.ofHom (specSectionsMap q)) = X.isoSpec.inv ≫ q := by
  rw [← isoSpec_inv_naturality q, isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

/-- The affine sections comparison together with its action on the original sections. -/
def affinePullbackSpecSectionsComparison {A B : Type u} [CommRing A] [CommRing B]
    {X : Scheme.{u}} [IsAffine X] (q : X ⟶ Spec (.of A)) (f : A →+* B) :
    let g := Spec.map (CommRingCat.ofHom f)
    let : Algebra A B := f.toAlgebra
    let : Algebra A Γ(X, ⊤) := (specSectionsMap q).toAlgebra
    let : Algebra B Γ(pullback q g, ⊤) := (specSectionsMap (pullback.snd q g)).toAlgebra
    {e : B ⊗[A] Γ(X, ⊤) ≃ₐ[B] Γ(pullback q g, ⊤) //
      ∀ s : Γ(X, ⊤), e ((1 : B) ⊗ₜ[A] s) = (pullback.fst q g).appTop s} := by
  dsimp only
  let g := Spec.map (CommRingCat.ofHom f)
  let T : Type u := Γ(X, ⊤)
  let : Algebra A B := f.toAlgebra
  let : Algebra A T := (specSectionsMap q).toAlgebra
  let : Algebra B Γ(pullback q g, ⊤) := (specSectionsMap (pullback.snd q g)).toAlgebra
  let q₀ := Spec.map (CommRingCat.ofHom (algebraMap A T))
  let a : Spec (.of (B ⊗[A] T)) ⟶ Spec (.of T) :=
    Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom)
  let b := Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[A] T)))
  have h : IsPullback a b q₀ g :=
    (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A B T)).flip
  have h' : IsPullback (a ≫ X.isoSpec.inv) b q g := by
    refine h.of_iso (Iso.refl _) X.isoSpec.symm (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) ?_ (by simp)
    change Spec.map (CommRingCat.ofHom (specSectionsMap q)) ≫ 𝟙 _ = X.isoSpec.inv ≫ q
    rw [Category.comp_id, Spec_map_specSectionsMap]
  let i : Γ(Spec (.of (B ⊗[A] T)), ⊤) ≅ Γ(pullback q g, ⊤) :=
    { hom := h'.isoPullback.inv.appTop
      inv := h'.isoPullback.hom.appTop
      hom_inv_id := by rw [← Scheme.Hom.comp_appTop]; simp
      inv_hom_id := by rw [← Scheme.Hom.comp_appTop]; simp }
  let e := (Scheme.ΓSpecIso (.of (B ⊗[A] T))).symm ≪≫ i
  have he : CommRingCat.ofHom (algebraMap B (B ⊗[A] T)) ≫ e.hom =
      (Scheme.ΓSpecIso (.of B)).inv ≫ (pullback.snd q g).appTop := by
    change _ ≫ (Scheme.ΓSpecIso (.of (B ⊗[A] T))).inv ≫ h'.isoPullback.inv.appTop = _
    rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc,
      ← Scheme.Hom.comp_appTop, h'.isoPullback_inv_snd]
  refine ⟨{ e.commRingCatIsoToRingEquiv with
    commutes' := fun s ↦ congrArg (fun k : CommRingCat.of B ⟶ Γ(pullback q g, ⊤) ↦
      k.hom s) he }, fun s ↦ ?_⟩
  have hfst : h'.isoPullback.inv ≫ a = pullback.fst q g ≫ X.isoSpec.hom := by
    apply (cancel_mono X.isoSpec.inv).mp
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h'.isoPullback_inv_fst
  have hs : CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom ≫ e.hom =
      (pullback.fst q g).appTop := by
    change _ ≫ (ΓSpecIso (.of (B ⊗[A] T))).inv ≫ h'.isoPullback.inv.appTop = _
    rw [← Category.assoc, ΓSpecIso_inv_naturality, Category.assoc, ← Hom.comp_appTop,
      hfst, Hom.comp_appTop, ← Category.assoc, isoSpec_hom, toSpecΓ_appTop]
    change ((ΓSpecIso Γ(X, ⊤)).inv ≫ (ΓSpecIso Γ(X, ⊤)).hom) ≫ _ = _
    rw [Iso.inv_hom_id, Category.id_comp]
  exact congrArg (fun k : Γ(X, ⊤) ⟶ Γ(pullback q g, ⊤) ↦ k.hom s) hs

/-- Actual base change of an affine scheme over a spectrum on global sections. -/
def affinePullbackSpecSectionsAlgEquiv {A B : Type u} [CommRing A] [CommRing B]
    {X : Scheme.{u}} [IsAffine X] (q : X ⟶ Spec (.of A)) (f : A →+* B) :
    let g := Spec.map (CommRingCat.ofHom f)
    let : Algebra A B := f.toAlgebra
    let : Algebra A Γ(X, ⊤) := (specSectionsMap q).toAlgebra
    let : Algebra B Γ(pullback q g, ⊤) := (specSectionsMap (pullback.snd q g)).toAlgebra
    B ⊗[A] Γ(X, ⊤) ≃ₐ[B] Γ(pullback q g, ⊤) :=
  (affinePullbackSpecSectionsComparison q f).1

/-- The right tensor factor pulls back along the original first projection. -/
theorem affinePullbackSpecSectionsAlgEquiv_one_tmul {A B : Type u} [CommRing A] [CommRing B]
    {X : Scheme.{u}} [IsAffine X] (q : X ⟶ Spec (.of A)) (f : A →+* B) (s : Γ(X, ⊤)) :
    let g := Spec.map (CommRingCat.ofHom f)
    let : Algebra A B := f.toAlgebra
    let : Algebra A Γ(X, ⊤) := (specSectionsMap q).toAlgebra
    let : Algebra B Γ(pullback q g, ⊤) := (specSectionsMap (pullback.snd q g)).toAlgebra
    affinePullbackSpecSectionsAlgEquiv q f ((1 : B) ⊗ₜ[A] s) =
      (pullback.fst q g).appTop s :=
  (affinePullbackSpecSectionsComparison q f).2 s

/-- The section comparison for a pullback followed by a change of affine coordinates. -/
def affinePullbackSpecSectionsCompAlgEquiv {A B : Type u} [CommRing A] [CommRing B]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Spec (.of A) ⟶ Y) [IsAffine (pullback f g)]
    (φ : A →+* B) :
    let l := Spec.map (CommRingCat.ofHom φ)
    let : Algebra A B := φ.toAlgebra
    let : Algebra A Γ(pullback f g, ⊤) := (specSectionsMap (pullback.snd f g)).toAlgebra
    let : Algebra B Γ(pullback f (l ≫ g), ⊤) :=
      (specSectionsMap (pullback.snd f (l ≫ g))).toAlgebra
    B ⊗[A] Γ(pullback f g, ⊤) ≃ₐ[B] Γ(pullback f (l ≫ g), ⊤) := by
  dsimp only
  let l := Spec.map (CommRingCat.ofHom φ)
  let n := pullback.snd f g
  let q := pullback.snd f (l ≫ g)
  let q' := pullback.snd n l
  let : Algebra A B := φ.toAlgebra
  let : Algebra A Γ(pullback f g, ⊤) := (specSectionsMap n).toAlgebra
  let : Algebra B Γ(pullback n l, ⊤) := (specSectionsMap q').toAlgebra
  let : Algebra B Γ(pullback f (l ≫ g), ⊤) := (specSectionsMap q).toAlgebra
  let e := pullbackLeftPullbackSndIso f g l
  have hq : e.inv ≫ q' = q := pullbackLeftPullbackSndIso_inv_snd_snd f g l
  let i : Γ(pullback (pullback.snd f g) l, ⊤) ≅ Γ(pullback f (l ≫ g), ⊤) :=
    { hom := e.inv.appTop
      inv := e.hom.appTop
      hom_inv_id := by rw [← Scheme.Hom.comp_appTop]; simp
      inv_hom_id := by rw [← Scheme.Hom.comp_appTop]; simp }
  let iB : Γ(pullback n l, ⊤) ≃ₐ[B] Γ(pullback f (l ≫ g), ⊤) :=
    { i.commRingCatIsoToRingEquiv with
      commutes' := fun b ↦ by
        change ((ΓSpecIso (.of B)).inv ≫ q'.appTop ≫ e.inv.appTop).hom b =
          ((ΓSpecIso (.of B)).inv ≫ q.appTop).hom b
        rw [← Scheme.Hom.comp_appTop, hq] }
  exact (affinePullbackSpecSectionsAlgEquiv n φ).trans iB

end AlgebraicGeometry.Scheme
