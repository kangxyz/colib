/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.PrincipalSection.Naturality
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.FiniteSupport

/-!
# Laurent power cuts over a quasi-compact base

Pulling the support back over the terms of a finite affine cover restricts the
original forward coordinate, unit, and zero-scheme projection. The maximum of
finitely many affine bounds works for the original projection.

See Voevodsky, *Cancellation theorem*, Lemma 4.1 and Remark 4.2.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial

open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.AffineLineFiber (point)

variable {k : Type u} [Field k] {X P : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (g : P ⟶ pullback f (multiplicativeGroupBaseChange (Spec (.of k)) ↘ Spec (.of k)))

set_option quotPrecheck false in
local notation "τ" => (multiplicativeGroupBaseChange (Spec (.of k)) ↘ Spec (.of k))
set_option quotPrecheck false in
local notation "p" => (g ≫ pullback.fst f τ)
set_option quotPrecheck false in
local notation "t" => (g ≫ pullback.snd f τ).appTop
  (multiplicativeGroupBaseChangeCoordinate (Spec (.of k))).val
set_option quotPrecheck false in
local notation "Aₚ" => Γ(P, ⊤)

private abbrev cutProjection {D A : Scheme.{u}} (b : A ⟶ Spec (.of k))
    (a : D ⟶ A) (s : Γ(D, ⊤)) :
    Scheme.AffineLineFiber.fiber (sectionToAffineLine (a ≫ b) s) 0 ⟶ A :=
  Scheme.AffineLineFiber.inclusion (sectionToAffineLine (a ≫ b) s) 0 ≫ a

private def ambientRestrict {R : Type u} [CommRing R] (j : Spec (.of R) ⟶ X) :
    ambient (j ≫ f) ⟶ pullback f τ :=
  (pullbackRightPullbackFstIso f τ j).inv ≫
    pullback.snd j (pullback.fst f τ)

private theorem isPullback_ambientRestrict {R : Type u} [CommRing R]
    (j : Spec (.of R) ⟶ X) :
    IsPullback (ambientRestrict f j) (pullback.fst (j ≫ f) τ)
      (pullback.fst f τ) j := by
  apply (IsPullback.of_hasPullback j (pullback.fst f τ)).flip.of_iso'
    (pullbackRightPullbackFstIso f τ j).symm (.refl _) (.refl _) (.refl _)
  · simp [ambientRestrict]
  · simp
  · simp
  · simp

private abbrev restrictedSupport {R : Type u} [CommRing R] (j : Spec (.of R) ⟶ X) :
    pullback g (ambientRestrict f j) ⟶ ambient (j ≫ f) :=
  pullback.snd g (ambientRestrict f j)

private abbrev supportRestriction {R : Type u} [CommRing R] (j : Spec (.of R) ⟶ X) :
    pullback g (ambientRestrict f j) ⟶ P :=
  pullback.fst g (ambientRestrict f j)

private abbrev restrictedProjection {R : Type u} [CommRing R] (j : Spec (.of R) ⟶ X) :
    pullback g (ambientRestrict f j) ⟶ Spec (.of R) :=
  restrictedSupport f g j ≫ pullback.fst (j ≫ f) τ

private theorem isPullback_supportRestrict {R : Type u} [CommRing R]
    (j : Spec (.of R) ⟶ X) :
    IsPullback (supportRestriction f g j) (restrictedProjection f g j) p j :=
  (IsPullback.of_hasPullback g (ambientRestrict f j)).paste_vert
    (isPullback_ambientRestrict f j)

private theorem restrict_coordinate {R : Type u} [CommRing R] (j : Spec (.of R) ⟶ X) :
    (supportRestriction f g j).appTop t =
      (restrictedSupport f g j).appTop (ambientCoordinate (j ≫ f)).val := by
  let c := (multiplicativeGroupBaseChangeCoordinate (Spec (.of k))).val
  change (supportRestriction f g j).appTop ((g ≫ pullback.snd f _).appTop c) =
    (restrictedSupport f g j).appTop ((pullback.snd (j ≫ f) _).appTop c)
  simp only [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
  have h : supportRestriction f g j ≫ g = restrictedSupport f g j ≫ ambientRestrict f j :=
    pullback.condition
  rw [← Category.assoc, h, Category.assoc]
  have hs : ambientRestrict f j ≫ pullback.snd f τ =
      pullback.snd (j ≫ f) τ := by
    simp [ambientRestrict]
  rw [hs]

private theorem restrict_coefficient {R : Type u} [CommRing R] (j : Spec (.of R) ⟶ X)
    (a : Γ(X, ⊤)) :
    (supportRestriction f g j).appTop ((p).appTop a) = (restrictedProjection f g j).appTop
      ((ΓSpecIso (.of R)).inv ((ΓSpecIso (.of R)).hom (j.appTop a))) := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, (isPullback_supportRestrict f g j).w,
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Iso.hom_inv_id_apply]

private theorem isFinite_pullback_cut_of_isFinite_restriction {R : Type u} [CommRing R]
    (j : Spec (.of R) ⟶ X) (s : Aₚ)
    (hs : IsFinite (cutProjection (j ≫ f) (restrictedProjection f g j)
      ((supportRestriction f g j).appTop s))) :
    IsFinite (pullback.snd (cutProjection f p s) j) := by
  let F := sectionToAffineLine (p ≫ f) s
  let v := supportRestriction f g j
  let h := isPullback_supportRestrict f g j
  have he : restrictedProjection f g j ≫ j ≫ f = v ≫ p ≫ f := (h.w_assoc f).symm
  have hF : sectionToAffineLine (restrictedProjection f g j ≫ j ≫ f) (v.appTop s) =
      v ≫ F := by
    rw [he, ← Category.assoc v p f]
    exact sectionToAffineLine_comp v (p ≫ f) s
  dsimp only [cutProjection] at hs
  rw [hF] at hs
  let e := pullbackLeftPullbackSndIso (point (0 : k)) F v
  let z := e.inv ≫ pullback.fst (Scheme.AffineLineFiber.inclusion F 0) v
  have hz : IsPullback z (Scheme.AffineLineFiber.inclusion (v ≫ F) 0)
      (Scheme.AffineLineFiber.inclusion F 0) v := by
    apply (IsPullback.of_hasPullback (Scheme.AffineLineFiber.inclusion F 0) v).of_iso' e.symm
      (.refl _) (.refl _) (.refl _)
    · simp [z]
    · simp [e]
    · simp
    · simp
  have hh := hz.paste_vert h
  change IsFinite (pullback.snd (Scheme.AffineLineFiber.inclusion F 0 ≫ p) j)
  rw [← hh.isoPullback_inv_snd, MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite.{u})]
  exact hs

private theorem exists_finite_affineOpenCover (X : Scheme.{u}) [CompactSpace X] :
    ∃ C : Scheme.AffineOpenCover.{u, u} X, Finite C.I₀ := by
  let U := X.affineOpenCover
  let V := U.openCover.finiteSubcover
  let C : Scheme.AffineOpenCover.{u, u} X :=
    { I₀ := V.I₀
      X := fun i => U.X (U.openCover.idx i.1)
      f := V.f
      idx := V.idx
      covers := V.covers
      map_prop := V.map_prop }
  exact ⟨C, inferInstanceAs (Finite U.openCover.finiteSubcover.I₀)⟩

/-- On a support finite over the native torus over a quasi-compact scheme, the
original zero scheme of `t ^ n - u` is finite over the scheme for all large `n`. -/
@[colib_tag "COL-1040", colib_ref "Voevodsky2010Cancellation" "Lemma 4.1, p. 680"
  "adaptation" "Finite support of the denominator zero scheme"]
theorem exists_isFinite_power_sub_unit_of_compactSpace [CompactSpace X] [IsFinite g]
    (u₀ : Aₚˣ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      IsFinite (Scheme.AffineLineFiber.inclusion
        (sectionToAffineLine (p ≫ f) (t ^ n - (u₀ : Aₚ))) 0 ≫ p) := by
  classical
  obtain ⟨C, hC⟩ := exists_finite_affineOpenCover X
  let : Fintype C.I₀ := Fintype.ofFinite _
  let j := C.f
  let uᵢ (i : C.I₀) :=
    Units.map (supportRestriction f g (R := C.X i) (j i)).appTop.hom.toMonoidHom u₀
  choose N hN using fun i => exists_isFinite_power_sub_unit (R := C.X i) (j i ≫ f)
    (restrictedSupport f g (R := C.X i) (j i)) (uᵢ i)
  refine ⟨Finset.univ.sup N, fun n hn => ?_⟩
  apply (IsZariskiLocalAtTarget.iff_of_openCover (P := @IsFinite.{u}) C.openCover).mpr
  intro i
  change C.I₀ at i
  apply isFinite_pullback_cut_of_isFinite_restriction f g (R := C.X i) (j i)
  let v := supportRestriction f g (R := C.X i) (j i)
  let w := (restrictedSupport f g (R := C.X i) (j i)).appTop
    (ambientCoordinate (j i ≫ f)).val
  have he : v.appTop (t ^ n - (u₀ : Aₚ)) = w ^ n - (uᵢ i).val := by
    rw [map_sub, map_pow]
    exact congrArg (fun z => z ^ n - (uᵢ i).val) (restrict_coordinate f g (j i))
  exact he.symm ▸ hN i n ((Finset.le_sup (Finset.mem_univ i)).trans hn)

/-- On a support finite over the native torus over a quasi-compact scheme, the
original zero scheme of `t ^ n - 1` is finite over the scheme for positive `n`. -/
@[colib_tag "COL-1040", colib_ref "Voevodsky2010Cancellation" "Lemma 4.1, p. 680"
  "adaptation" "Finite support of the numerator zero scheme"]
theorem isFinite_power_sub_one_of_compactSpace [CompactSpace X] [IsFinite g]
    {n : ℕ} (hn : 0 < n) : IsFinite (Scheme.AffineLineFiber.inclusion
      (sectionToAffineLine (p ≫ f) (t ^ n - (1 : Aₚ))) 0 ≫ p) := by
  obtain ⟨C, _⟩ := exists_finite_affineOpenCover X
  let j := C.f
  apply (IsZariskiLocalAtTarget.iff_of_openCover (P := @IsFinite.{u}) C.openCover).mpr
  intro i
  change C.I₀ at i
  apply isFinite_pullback_cut_of_isFinite_restriction f g (R := C.X i) (j i)
  let v := supportRestriction f g (R := C.X i) (j i)
  let w := (restrictedSupport f g (R := C.X i) (j i)).appTop
    (ambientCoordinate (j i ≫ f)).val
  have he : v.appTop (t ^ n - (1 : Aₚ)) = w ^ n - 1 := by
    rw [map_sub, map_pow, map_one]
    exact congrArg (fun z => z ^ n - 1) (restrict_coordinate f g (j i))
  exact he.symm ▸ isFinite_power_sub_one (R := C.X i) (j i ≫ f)
    (restrictedSupport f g (R := C.X i) (j i)) hn

/-- The original zero scheme of the interpolated numerator is finite over a
quasi-compact base for two large exponents, uniformly in its global coefficient. -/
@[colib_tag "COL-1040", colib_ref "Voevodsky2010Cancellation" "Remark 4.2, p. 680"
  "adaptation" "Uniform finite support of the interpolated numerator"]
theorem exists_isFinite_power_cut_family_of_compactSpace [CompactSpace X] [IsFinite g]
    (u₀ : Aₚˣ) : ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n → ∀ a : Γ(X, ⊤),
      IsFinite (Scheme.AffineLineFiber.inclusion (sectionToAffineLine (p ≫ f)
        ((p).appTop a * (t ^ m - 1) * (t ^ n - (u₀ : Aₚ)) +
          (1 - (p).appTop a) * (t ^ n - 1) * (t ^ m - (u₀ : Aₚ)))) 0 ≫ p) := by
  classical
  obtain ⟨C, hC⟩ := exists_finite_affineOpenCover X
  let : Fintype C.I₀ := Fintype.ofFinite _
  let j := C.f
  let uᵢ (i : C.I₀) :=
    Units.map (supportRestriction f g (R := C.X i) (j i)).appTop.hom.toMonoidHom u₀
  choose N hN using fun i => exists_isFinite_power_cut_family (R := C.X i) (j i ≫ f)
    (restrictedSupport f g (R := C.X i) (j i)) (uᵢ i)
  refine ⟨Finset.univ.sup N, fun m n hm hn a => ?_⟩
  apply (IsZariskiLocalAtTarget.iff_of_openCover (P := @IsFinite.{u}) C.openCover).mpr
  intro i
  change C.I₀ at i
  apply isFinite_pullback_cut_of_isFinite_restriction f g (R := C.X i) (j i)
  let v := supportRestriction f g (R := C.X i) (j i)
  let w := (restrictedSupport f g (R := C.X i) (j i)).appTop
    (ambientCoordinate (j i ≫ f)).val
  let b := (restrictedProjection f g (j i)).appTop
    ((ΓSpecIso (C.X i)).inv ((ΓSpecIso (C.X i)).hom ((j i).appTop a)))
  have he : v.appTop ((p).appTop a * (t ^ m - 1) * (t ^ n - (u₀ : Aₚ)) +
      (1 - (p).appTop a) * (t ^ n - 1) * (t ^ m - (u₀ : Aₚ))) =
      b * (w ^ m - 1) * (w ^ n - (uᵢ i).val) + (1 - b) * (w ^ n - 1) * (w ^ m - (uᵢ i).val) := by
    change (supportRestriction f g (j i)).appTop _ = _
    simp only [map_add, map_mul, map_sub, map_pow, map_one,
      restrict_coefficient f g (R := C.X i) (j i), restrict_coordinate f g (R := C.X i) (j i)]
    rfl
  exact he.symm ▸ hN i m n ((Finset.le_sup (Finset.mem_univ i)).trans hm)
    ((Finset.le_sup (Finset.mem_univ i)).trans hn) ((ΓSpecIso (C.X i)).hom ((j i).appTop a))

end AlgebraicGeometry.NativeTorusPolynomial
