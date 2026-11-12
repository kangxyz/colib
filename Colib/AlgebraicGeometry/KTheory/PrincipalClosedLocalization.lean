/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.CoherentAffineLocalizationSequence
public import Colib.AlgebraicGeometry.KTheory.CoherentPrincipalClosedDevissage

/-!
# Principal closed-open coherent G-localization

The closed map is the original coherent direct image along the principal
quotient. The boundary is the actual geometric localization boundary followed
by the inverse of the proved closed-to-supported dévissage map. All groups use
the public scheme G-theory universe. No annihilated category is identified
with the whole supported category before dévissage.

Implementation source: `Quillen/AlgebraicGeometry/Scheme/PrincipalClosedGTheory.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.ExactCategory
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.PrincipalClosed
variable (R : CommRingCat.{u}) [IsNoetherianRing R] (f : R)

/-- The actual geometric direct image along the principal closed immersion. -/
abbrev pushforwardG (n : ℕ) :
    G (Spec (CommRingCat.of (FGModuleCat.ClosedRing f))) n →* G (Spec R) n :=
  Scheme.closedPushforwardG
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))) n

/-- The original geometric connecting map with values in the actual closed scheme. -/
def boundaryG (n : ℕ) :
    G (Spec (CommRingCat.of (Localization.Away f))) (n + 1) →*
      G (Spec (CommRingCat.of (FGModuleCat.ClosedRing f))) n :=
  (Modules.Coherent.PrincipalClosed.closedSupportGEquiv R f n).symm.toMonoidHom.comp
    (affineLocalizationBoundaryG R (Submonoid.powers f) n)

/-- Exactness at the ambient scheme, retaining actual closed direct image and open pullback. -/
theorem pushforward_range_eq_restrict_ker (n : ℕ) :
    (pushforwardG R f n).range =
      (pullbackG (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))) n).ker := by
  have he := Modules.Coherent.PrincipalClosed.closedSupportGEquiv_pushforward R f n
  have h : ((affineLocalizationInclusionG R (Submonoid.powers f) n).comp
      (Modules.Coherent.PrincipalClosed.closedSupportGEquiv R f n).toMonoidHom).range =
      (pullbackG (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))) n).ker := by
    rw [MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr
        (Modules.Coherent.PrincipalClosed.closedSupportGEquiv R f n).surjective,
      ← MonoidHom.range_eq_map]
    exact (affineLocalization_longExact R (Submonoid.powers f)).1 n
  exact (congrArg MonoidHom.range he).symm.trans h

/-- Exactness at the principal open for the original geometric boundary. -/
theorem restrict_range_eq_boundary_ker (n : ℕ) :
    (pullbackG (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f))))
      (n + 1)).range = (boundaryG R f n).ker := by
  rw [(affineLocalization_longExact R (Submonoid.powers f)).2.1 n]
  ext x
  simp only [MonoidHom.mem_ker, boundaryG, MonoidHom.comp_apply,
    MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
  constructor
  · intro h
    rw [h, map_one]
  · intro h
    apply (Modules.Coherent.PrincipalClosed.closedSupportGEquiv R f n).symm.injective
    simpa only [map_one] using h

set_option maxHeartbeats 1000000 in
-- The original closed-support equivalence retains its actual small-model exact functor.
/-- Exactness at the actual closed scheme, by the proved direct-image dévissage map. -/
theorem boundary_range_eq_pushforward_ker (n : ℕ) :
    (boundaryG R f n).range = (pushforwardG R f n).ker := by
  let e := Modules.Coherent.PrincipalClosed.closedSupportGEquiv R f n
  have he := Modules.Coherent.PrincipalClosed.closedSupportGEquiv_pushforward R f n
  ext x
  rw [MonoidHom.mem_range, MonoidHom.mem_ker]
  constructor
  · rintro ⟨y, rfl⟩
    have hy : affineLocalizationBoundaryG R (Submonoid.powers f) n y ∈
        (affineLocalizationInclusionG R (Submonoid.powers f) n).ker := by
      rw [← (affineLocalization_longExact R (Submonoid.powers f)).2.2.1 n]
      exact ⟨y, rfl⟩
    have hx := DFunLike.congr_fun he (boundaryG R f n y)
    simp only [MonoidHom.comp_apply, boundaryG, MulEquiv.toMonoidHom_eq_coe,
      MonoidHom.coe_ofClass, MulEquiv.apply_symm_apply] at hx
    exact hx.symm.trans hy
  · intro hx
    have hy : e x ∈ (affineLocalizationInclusionG R (Submonoid.powers f) n).ker := by
      change affineLocalizationInclusionG R (Submonoid.powers f) n (e x) = 1
      exact (DFunLike.congr_fun he x).trans hx
    rw [← (affineLocalization_longExact R (Submonoid.powers f)).2.2.1 n] at hy
    obtain ⟨y, hy⟩ := hy
    refine ⟨y, ?_⟩
    change e.symm (affineLocalizationBoundaryG R (Submonoid.powers f) n y) = x
    exact (congrArg e.symm hy).trans (e.symm_apply_apply x)

/-- The complete principal closed-open connective sequence, with its degree-zero surjection. -/
theorem localization_longExact :
    (∀ n, (pushforwardG R f n).range =
      (pullbackG (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))) n).ker) ∧
    (∀ n, (pullbackG (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f))))
      (n + 1)).range = (boundaryG R f n).ker) ∧
    (∀ n, (boundaryG R f n).range = (pushforwardG R f n).ker) ∧
    Function.Surjective
      (pullbackG (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))) 0) :=
  ⟨pushforward_range_eq_restrict_ker R f, restrict_range_eq_boundary_ker R f,
    boundary_range_eq_pushforward_ker R f,
    (affineLocalization_longExact R (Submonoid.powers f)).2.2.2⟩

/-- The ambient exactness assertion with the original open-restriction spelling. -/
theorem pushforward_range_eq_openRestriction_ker (n : ℕ) :
    (pushforwardG R f n).range =
      (restrictG (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))) n).ker := by
  rw [← pullbackG_eq_restrictG]
  exact pushforward_range_eq_restrict_ker R f n

/-- The open exactness assertion with the original geometric restriction map. -/
theorem openRestriction_range_eq_boundary_ker (n : ℕ) :
    (restrictG (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f))))
      (n + 1)).range = (boundaryG R f n).ker := by
  rw [← pullbackG_eq_restrictG]
  exact restrict_range_eq_boundary_ker R f n

end AlgebraicGeometry.Scheme.PrincipalClosed

attribute [colib_tag "COL-0612",
  colib_ref "WeibelKBook" "V, Devissage Theorem 4.1 and proof, page 33" "specialization"
    "Actual principal quotient direct image and finite image-filtration devissage",
  colib_ref "WeibelKBook" "V, Theorem 5.1, page 35" "specialization"
    "Principal closed-open coherent localization on noetherian affine schemes"]
  AlgebraicGeometry.Scheme.PrincipalClosed.localization_longExact
  AlgebraicGeometry.Scheme.PrincipalClosed.pushforward_range_eq_openRestriction_ker
  AlgebraicGeometry.Scheme.PrincipalClosed.openRestriction_range_eq_boundary_ker
  AlgebraicGeometry.Scheme.PrincipalClosed.boundary_range_eq_pushforward_ker
