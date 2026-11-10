/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.PolynomialProducts

/-!
# Principal equations and exact quotient lengths in the retained native ambient

These are the kernel ideal stalks of the original native inclusion, not stalks
of an unproved replacement model. The explicit coordinate-chart isomorphism
transports the complete principal ideal. Above each generic source point, the
quotient length is finite and is the actual correspondence coefficient.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Polynomial TopologicalSpace Stacks.Chow

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial

variable {S : Scheme.{u}} {R : Type u} [CommRing R]

attribute [local instance] ambient_isAffine inclusion_isClosedImmersion

theorem chartMap_appTop_polynomial (f : Spec (.of R) ⟶ S) (p : R[X]) :
    (nativeChartIso f).hom.appTop (ambientPolynomial f p) =
      (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv (toLaurent p) := by
  have h := congrArg (fun k : LaurentPolynomial R →+* Γ(Spec (.of (LaurentPolynomial R)), ⊤) =>
    k (toLaurent p)) (chartMap_appTop_chartRingHom f)
  simpa only [RingHom.comp_apply, chartRingHom, LaurentPolynomial.eval₂_toLaurent,
    ambientPolynomial, coe_eval₂RingHom, nativeChartIso] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The whole native closed image is defined by the original polynomial section. -/
theorem inclusion_ker_top (f : Spec (.of R) ⟶ S) (p : R[X])
    (hu : IsUnit (p.coeff 0)) :
    (inclusion f p hu).ker.ideal ⟨⊤, isAffineOpen_top (ambient f)⟩ =
      Ideal.span {ambientPolynomial f p} := by
  rw [Scheme.Hom.ker_apply]
  change RingHom.ker (inclusion f p hu).appTop.hom = Ideal.span {ambientPolynomial f p}
  have hc := congrArg (fun k => k.appTop.hom) (chartQuotient_chartMap f p hu)
  rw [Scheme.Hom.comp_appTop] at hc
  change (chartQuotient p hu).appTop.hom.comp (nativeChartIso f).hom.appTop.hom =
    (inclusion f p hu).appTop.hom at hc
  rw [← hc, ← RingHom.comap_ker]
  have hq := chartQuotient_ker_top p hu
  rw [Scheme.Hom.ker_apply] at hq
  change RingHom.ker (chartQuotient p hu).appTop.hom =
    Ideal.span {(Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv (toLaurent p)} at hq
  rw [hq]
  have hm : Ideal.span {(Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv (toLaurent p)} =
      (Ideal.span {ambientPolynomial f p}).map (nativeChartIso f).hom.appTop.hom := by
    rw [Ideal.map_span, Set.image_singleton, chartMap_appTop_polynomial]
  rw [hm, Ideal.comap_map_of_bijective _
    (ConcreteCategory.bijective_of_isIso (nativeChartIso f).hom.appTop)]

/-- The original polynomial section in a stalk of the actual native torus ambient. -/
def nativePolynomialGerm (f : Spec (.of R) ⟶ S) (p : R[X]) (x : ambient f) :
    (ambient f).presheaf.stalk x :=
  (ambient f).presheaf.germ ⊤ x (by trivial) (ambientPolynomial f p)

/-- Exact native stalk quotient identification, with all nilpotents retained. -/
theorem inclusion_ker_stalk (f : Spec (.of R) ⟶ S) (p : R[X])
    (hu : IsUnit (p.coeff 0)) (x : ambient f) :
    IdealSheafData.stalk (inclusion f p hu).ker x = Ideal.span {nativePolynomialGerm f p x} := by
  rw [IdealSheafData.stalk_eq_map_germ _ x ⟨⊤, isAffineOpen_top (ambient f)⟩ (by trivial),
    inclusion_ker_top, Ideal.map_span, Set.image_singleton]
  rfl

@[simp] theorem nativePolynomialGerm_mul (f : Spec (.of R) ⟶ S)
    (p q : R[X]) (x : ambient f) :
    nativePolynomialGerm f (p * q) x = nativePolynomialGerm f p x * nativePolynomialGerm f q x := by
  simp only [nativePolynomialGerm, map_mul]

/-- Full quotient length over the actual native ambient stalk. -/
def nativeQuotientStalkLength (f : Spec (.of R) ⟶ S) (p : R[X]) (x : ambient f) : ℕ∞ :=
  Module.length ((ambient f).presheaf.stalk x)
    ((ambient f).presheaf.stalk x ⧸ Ideal.span {nativePolynomialGerm f p x})

variable [IsNoetherianRing R]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every relevant native quotient length is finite, before taking integer coefficients. -/
theorem nativeQuotientStalkLength_ne_top (f : Spec (.of R) ⟶ S)
    (p : R[X]) (hp : p.Monic) (hu : IsUnit (p.coeff 0)) (x : ambient f)
    (hx : pullback.fst f (multiplicativeGroupBaseChange S ↘ S) x ∈
      genericPoints (Spec (.of R))) : nativeQuotientStalkLength f p x ≠ ⊤ := by
  have := quotient_isNoetherian p
  have : IsFinite (inclusion f p hu ≫ pullback.fst _ _) := by
    rw [inclusion_fst]
    exact projection_isFinite p hp
  have h := closedImmersionQuotientStalkLength_ne_top (C := ambient f)
    (pullback.fst _ _) (inclusion f p hu) x hx
  have he := congrArg (fun I : Ideal ((ambient f).presheaf.stalk x) =>
    Module.length ((ambient f).presheaf.stalk x)
      (((ambient f).presheaf.stalk x) ⧸ I)) (inclusion_ker_stalk f p hu x)
  exact fun ht => h (he.trans ht)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual native cycle coefficient equals its actual finite native-stalk quotient length. -/
theorem polynomialCycle_apply_native (f : Spec (.of R) ⟶ S)
    (p : R[X]) (hp : p.Monic) (hu : IsUnit (p.coeff 0)) (x : ambient f)
    (hx : pullback.fst f (multiplicativeGroupBaseChange S ↘ S) x ∈
      genericPoints (Spec (.of R))) :
    (polynomialCycle f p hp hu).val x = ((nativeQuotientStalkLength f p x).toNat : ℤ) := by
  have := quotient_isNoetherian p
  have : IsFinite (inclusion f p hu ≫ pullback.fst _ _) := by
    rw [inclusion_fst]
    exact projection_isFinite p hp
  rw [polynomialCycle_val,
    finiteCyclePushforward_fundamentalCycle_apply_eq_quotientStalkLength (C := ambient f)
      (pullback.fst _ _) (inclusion f p hu) x hx]
  have he := congrArg (fun I : Ideal ((ambient f).presheaf.stalk x) =>
    Module.length ((ambient f).presheaf.stalk x)
      (((ambient f).presheaf.stalk x) ⧸ I)) (inclusion_ker_stalk f p hu x)
  exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) he

end AlgebraicGeometry.NativeTorusPolynomial
