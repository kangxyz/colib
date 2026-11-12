/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.PolynomialQuotient.Basic
public import Colib.AlgebraicGeometry.Sites.Smooth.Affine.Basic

/-!
# Smooth-site polynomial quotient maps
-/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Aglib/AlgebraicGeometry/Spec/PolynomialQuotient/SmoothSite.lean`, blob
`e594042bb4a78cbb82e8f5930cb8597bf6f71517`.
The source is the actual original scheme or ordinary free-Yoneda Ext group.
All monic quotient fibers retain their full scheme structure.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.PolynomialOpenQuotient
universe u
namespace AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
open _root_.AlgebraicGeometry.Scheme
variable {k R A : Type u} [Field k] [CommRing R] [CommRing A]
    [Algebra k R] [Algebra.Smooth k R] [Algebra R A] [Algebra k A]
    [IsScalarTower k R A] [Algebra.Smooth k A]

/-- The affine coefficient scheme `Spec A` as an object of the smooth site over `k`. -/
abbrev sourceSite := SmoothSite.affineSite k A

/-- The target is the actual relative affine line, still regarded over k. -/
abbrev lineSite : SmoothSite (Spec (.of k)) := by
  let : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k R))) :=
    SmoothSite.affineBaseMap_smooth (k := k) (R := R)
  let : Algebra.Smooth R R[X] := {}
  let : Smooth (polynomialProjection (.of R)) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)
  exact SmoothSite.mk (polynomialProjection (.of R) ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)))

/-- The unchanged principal open of the relative line. -/
abbrev openSite (f : R[X]) : SmoothSite (Spec (.of k)) := by
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  exact SmoothSite.mk ((principalOpen f).ι ≫ (lineSite (k := k) (R := R)).hom)

/-- The literal smooth-site inclusion of the principal open defined by `f` into the relative
line. -/
def openInclusion (f : R[X]) : openSite (k := k) f ⟶ lineSite (k := k) (R := R) :=
  SmoothSite.homMk (principalOpen f).ι rfl

omit [Algebra.Smooth k R] in
/-- The original coefficient tower agrees with the literal structure map. -/
theorem coefficient_base :
    Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k R)) =
        (sourceSite (k := k) (A := A)).hom := by
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact congrArg (fun φ : k →+* A => φ r) (IsScalarTower.algebraMap_eq k R A).symm

/-- Relative target coordinates preserve the original k-structure. -/
theorem span_base (p : A[X]) (f : R[X])
    (hf : IsUnit (AdjoinRoot.mk p (f.map (algebraMap R A)))) :
    source p ≫ (sourceSite (k := k) (A := A)).hom =
      openTarget (algebraMap R A) p f hf ≫ (openSite (k := k) f).hom := by
  rw [← coefficient_base (k := k) (R := R) (A := A)]
  change source p ≫ (_ ≫ _) = openTarget _ _ _ _ ≫ ((principalOpen f).ι ≫ (_ ≫ _))
  rw [← Category.assoc, ← Category.assoc, openTarget_inclusion,
    ← Category.assoc, target_base]

/-- The actual relative target relation before restricting to an open. -/
theorem affine_base (p : A[X]) :
    source p ≫ (sourceSite (k := k) (A := A)).hom =
      target (algebraMap R A) p ≫ (lineSite (k := k) (R := R)).hom := by
  rw [← coefficient_base (k := k) (R := R) (A := A)]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)))
      (target_base (algebraMap R A) p)).symm.trans (Category.assoc _ _ _))


end AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
