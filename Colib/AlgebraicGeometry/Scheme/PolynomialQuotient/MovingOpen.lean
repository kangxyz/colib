/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.PolynomialQuotient.SmoothSite
public import Colib.AlgebraicGeometry.Scheme.PolynomialQuotient.ZeroCoordinates

/-!
# The whole linear quotient and nested polynomial opens

Adapted from `PolynomialQuotientCoordinates.lean` and `OpenRestriction.lean`
in `Motivic/Aglib/AlgebraicGeometry/Spec/PolynomialQuotient/`
at `motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`, blobs
`807d29ce5848922f60cd65075c194d31bdadcbb1` and
`dab3a7e70054ed9fcaf080817785b80384d0b2ac`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Polynomial

universe u

namespace AlgebraicGeometry.PolynomialOpenQuotient

variable {B R : Type u} [CommRing B] [CommRing R] (σ : B →+* R)

/-- The quotient's target is the original coordinate graph. -/
theorem target_linear (a : R) :
    target σ (X - C a) = source (X - C a) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom σ a)) := by
  unfold target inclusion source
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro r
    change AdjoinRoot.mk (X - C a) ((C r).map σ) =
      AdjoinRoot.of (X - C a) ((C r).eval₂ σ a)
    simp only [Polynomial.map_C, eval₂_C]
    rfl
  · change AdjoinRoot.mk (X - C a) (X.map σ) =
      AdjoinRoot.of (X - C a) (X.eval₂ σ a)
    rw [Polynomial.map_X, eval₂_X]
    have h := AdjoinRoot.eval₂_root (X - C a)
    simpa only [eval₂_sub, eval₂_X, eval₂_C, sub_eq_zero, AdjoinRoot.root] using h

end AlgebraicGeometry.PolynomialOpenQuotient

namespace AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite

open _root_.AlgebraicGeometry.Scheme

variable {k R A : Type u} [Field k] [CommRing R] [CommRing A]
    [Algebra k R] [Algebra.Smooth k R] [Algebra R A] [Algebra k A]
    [IsScalarTower k R A] [Algebra.Smooth k A]

/-- The actual inclusion D(fg) into D(f). -/
def narrowInclusion (f g : R[X]) : openSite (k := k) (f * g) ⟶ openSite (k := k) f :=
  SmoothSite.homMk (Scheme.homOfLE (Spec (.of R[X])) (PrimeSpectrum.basicOpen_mul_le_left f g)) (by
    change Scheme.homOfLE _ _ ≫ ((principalOpen f).ι ≫ _) = _
    rw [← Category.assoc, Scheme.homOfLE_ι]
    rfl)

@[reassoc (attr := simp)] theorem narrowInclusion_comp (f g : R[X]) :
    narrowInclusion (k := k) f g ≫ openInclusion (k := k) f = openInclusion (k := k) (f * g) := by
  apply MorphismProperty.Over.Hom.ext
  exact Scheme.homOfLE_ι _ (PrimeSpectrum.basicOpen_mul_le_left f g)

omit [Algebra.Smooth k R] [Algebra.Smooth k A] [IsScalarTower k R A] in
/-- The larger boundary remains a unit on the same entire quotient. -/
theorem old_boundary_unit (p : A[X]) (f g : R[X])
    (h : IsUnit (AdjoinRoot.mk p ((f * g).map (algebraMap R A)))) :
    IsUnit (AdjoinRoot.mk p (f.map (algebraMap R A))) := by
  rw [Polynomial.map_mul, map_mul] at h
  exact (IsUnit.mul_iff.mp h).1


end AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
