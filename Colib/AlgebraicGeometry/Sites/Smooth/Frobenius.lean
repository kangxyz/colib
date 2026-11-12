/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Morphisms.Smooth.RelativeFrobenius
public import Colib.AlgebraicGeometry.Sites.Smooth.Basic
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres

/-!
# Relative Frobenius between original smooth-site objects

The target is the native pullback along the original base's absolute Frobenius. Its structure
map is the native second projection. Smoothness, separatedness and finite type are inherited
by that actual base change. The displayed morphism is precisely the native relative Frobenius,
which is finite, flat and a universal homeomorphism. Over a field the twist of an integral
smooth-site object is integral by reducedness and the actual homeomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Frobenius

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic S p)
  (X : SmoothSite S)

/-- The original Frobenius pullback, bundled as an object of the same smooth site. -/
def frobeniusTwist : SmoothSite S :=
  mk (pullback.snd X.hom (absoluteFrobenius S p hS))

@[simp]
theorem frobeniusTwist_left :
    (frobeniusTwist p hS X).left = pullback X.hom (absoluteFrobenius S p hS) := rfl

@[simp]
theorem frobeniusTwist_hom :
    (frobeniusTwist p hS X).hom = pullback.snd X.hom (absoluteFrobenius S p hS) := rfl

/-- The native relative Frobenius, between the original smooth-site source and twist. -/
@[colib_tag "COL-1098", stacks 0CC9 "relative Frobenius on the original smooth site"]
def relativeFrobenius : X ⟶ frobeniusTwist p hS X :=
  homMk (_root_.AlgebraicGeometry.relativeFrobenius S p hS ((forget S).obj X)).left
    (_root_.AlgebraicGeometry.relativeFrobenius S p hS ((forget S).obj X)).w

@[simp]
theorem relativeFrobenius_left :
    (relativeFrobenius p hS X).left =
      (_root_.AlgebraicGeometry.relativeFrobenius S p hS ((forget S).obj X)).left := rfl

instance relativeFrobenius_isFinite : IsFinite (relativeFrobenius p hS X).left := by
  have : LocallyOfFiniteType ((forget S).obj X).hom :=
    inferInstanceAs (LocallyOfFiniteType X.hom)
  exact _root_.AlgebraicGeometry.relativeFrobenius_isFinite S p hS ((forget S).obj X)

instance relativeFrobenius_flat : Flat (relativeFrobenius p hS X).left := by
  have : Smooth ((forget S).obj X).hom := inferInstanceAs (Smooth X.hom)
  exact flat_relativeFrobenius_of_smooth S p hS ((forget S).obj X)

instance relativeFrobenius_universalHomeomorphism :
    UniversalHomeomorphism (relativeFrobenius p hS X).left := by
  change UniversalHomeomorphism
    (_root_.AlgebraicGeometry.relativeFrobenius S p hS ((forget S).obj X)).left
  infer_instance

instance relativeFrobenius_universallyInjective :
    UniversallyInjective (relativeFrobenius p hS X).left :=
  ((universalHomeomorphism_iff_integral_universallyInjective_surjective _).mp
    (relativeFrobenius_universalHomeomorphism p hS X)).2.1

/-- Over the original field an integral smooth source has an integral Frobenius twist;
reducedness comes from smoothness, and irreducibility from the actual homeomorphism. -/
instance frobeniusTwist_isIntegral {k : Type u} [Field k] (p : ℕ) [Fact p.Prime]
    (hk : IsInCharacteristic (Spec (.of k)) p) (X : SmoothSite (Spec (.of k)))
    [IsIntegral X.left] : IsIntegral (frobeniusTwist p hk X).left := by
  have : IsReduced (frobeniusTwist p hk X).left :=
    isReduced_of_smooth_of_isAffine (Y := Spec (.of k)) (frobeniusTwist p hk X).hom
  have hhomeo : IsHomeomorph (relativeFrobenius p hk X).left :=
    (relativeFrobenius_universalHomeomorphism p hk X).universally_isHomeomorph
      _ _ _ IsPullback.of_id_snd
  have : IrreducibleSpace (frobeniusTwist p hk X).left :=
    (IsHomeomorph.homeomorph (relativeFrobenius p hk X).left hhomeo).irreducibleSpace_iff.mp
      inferInstance
  exact (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme.SmoothSite
