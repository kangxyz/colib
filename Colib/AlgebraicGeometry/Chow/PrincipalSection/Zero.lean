/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.PrincipalSection

/-!
# The whole zero scheme of the zero section

The affine-line map of the zero section factors through the literal origin.
Its scheme-theoretic zero fibre therefore has an isomorphic inclusion.
The zero fibre inclusion of any section annihilates that section on global sections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Polynomial

universe u

namespace AlgebraicGeometry.Scheme

open AffineLineFiber

variable {k : Type u} [Field k] {P X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The map of the zero section is the given structural map followed by the origin. -/
theorem sectionToAffineLine_zero (b : P ⟶ Spec (.of k)) :
    sectionToAffineLine b 0 = b ≫ point 0 := by
  apply ext_to_Spec
  simp only [Scheme.Γ_map_op, Scheme.Hom.comp_appTop, ← Category.assoc]
  rw [sectionToAffineLine, ΓSpecIso_inv_ΓSpec_adjunction_homEquiv, point,
    ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro r
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.coe_evalRingHom,
      Polynomial.eval_C]
  · simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, Polynomial.coe_evalRingHom,
      Polynomial.eval_X, map_zero]

/-- The actual zero fibre inclusion sends the original section to zero. -/
theorem section_zero_inclusion_appTop
    (b : P ⟶ Spec (.of k)) (s : Γ(P, ⊤)) :
    (inclusion (sectionToAffineLine b s) 0).appTop s = 0 := by
  let f := sectionToAffineLine b s
  have he : inclusion f 0 ≫ f = pullback.fst (point 0) f ≫ point 0 :=
    pullback.condition.symm
  have he' := congrArg (fun g => g.appTop) he
  simp only [Scheme.Hom.comp_appTop] at he'
  have hX := ConcreteCategory.congr_hom he' ((ΓSpecIso (.of (Polynomial k))).inv Polynomial.X)
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply, sectionToAffineLine_coordinate] at hX
  rw [hX]
  have hp := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k)))).symm
    Polynomial.X
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at hp
  change (point (0 : k)).appTop ((ΓSpecIso (.of (Polynomial k))).inv Polynomial.X) = _ at hp
  rw [hp]
  simp

/-- A finite zero scheme over `X` on a support whose projection to `X` is not
finite is cut by a nonzero global section. -/
theorem section_ne_zero_of_isFinite_zero (b : P ⟶ Spec (.of k)) (p : P ⟶ X)
    (s : Γ(P, ⊤)) (hcut : IsFinite (inclusion (sectionToAffineLine b s) 0 ≫ p))
    (hp : ¬ IsFinite p) : s ≠ 0 := by
  intro hs
  subst s
  rw [sectionToAffineLine_zero] at hcut
  have h : IsPullback b (𝟙 P) (point 0) (b ≫ point 0) :=
    (IsPullback.of_horiz_isIso_mono (fst := 𝟙 P) (snd := b) (g := point 0)
      (CommSq.mk (by rw [Category.id_comp]))).flip
  have : IsFinite (h.isoPullback.hom ≫ inclusion (b ≫ point 0) 0 ≫ p) := inferInstance
  rw [← Category.assoc, h.isoPullback_hom_snd, Category.id_comp] at this
  exact hp this

end AlgebraicGeometry.Scheme
