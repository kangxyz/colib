/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.FrobeniusFunctor
public import Colib.AlgebraicGeometry.Morphisms.Frobenius.IteratedNaturality

/-!
# The actual iterated relative Frobenius on the original smooth site

The target and map are literally the native n-fold twist and relative Frobenius. Their
geometry follows from the proved native equality with successive relative Frobenius maps
and the native canonical base-change identifications, not an arbitrary replacement target.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Frobenius

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic S p)

/-- The original pullback along the native absolute Frobenius power. -/
def nFoldFrobeniusTwist (n : ℕ) (X : SmoothSite S) : SmoothSite S :=
  mk (pullback.snd X.hom (absoluteFrobeniusPow S p hS n))

/-- The native n-fold relative Frobenius, bundled in the original smooth site. -/
def nFoldRelativeFrobenius (n : ℕ) (X : SmoothSite S) :
    X ⟶ nFoldFrobeniusTwist p hS n X :=
  homMk (_root_.AlgebraicGeometry.nFoldRelativeFrobenius S p hS n ((forget S).obj X)).left
    (_root_.AlgebraicGeometry.nFoldRelativeFrobenius S p hS n ((forget S).obj X)).w

@[simp]
theorem nFoldRelativeFrobenius_left (n : ℕ) (X : SmoothSite S) :
    (nFoldRelativeFrobenius p hS n X).left =
      (_root_.AlgebraicGeometry.nFoldRelativeFrobenius S p hS n ((forget S).obj X)).left := rfl

private theorem finite_flat_universalHomeomorphism_of_isIso
    {A B : Scheme.{u}} (e : A ⟶ B) [IsIso e] :
    IsFinite e ∧ Flat e ∧ UniversalHomeomorphism e :=
  ⟨inferInstance, inferInstance,
    (universalHomeomorphism_iff_integral_universallyInjective_surjective e).mpr
      ⟨inferInstance, inferInstance, inferInstance⟩⟩

private theorem finite_flat_universalHomeomorphism_relativeFrobenius
    (A : Over S) [Smooth A.hom] :
    IsFinite (_root_.AlgebraicGeometry.relativeFrobenius S p hS A).left ∧
      Flat (_root_.AlgebraicGeometry.relativeFrobenius S p hS A).left ∧
      UniversalHomeomorphism (_root_.AlgebraicGeometry.relativeFrobenius S p hS A).left :=
  ⟨inferInstance, flat_relativeFrobenius_of_smooth S p hS A, inferInstance⟩

private theorem finite_flat_universalHomeomorphism_successive
    (A : Over S) [Smooth A.hom] (n : ℕ) :
    IsFinite (successiveRelativeFrobenius S p hS A n).left ∧
      Flat (successiveRelativeFrobenius S p hS A n).left ∧
      UniversalHomeomorphism (successiveRelativeFrobenius S p hS A n).left := by
  induction n with
  | zero =>
    obtain ⟨hf, hl, hu⟩ := finite_flat_universalHomeomorphism_relativeFrobenius p hS A
    simp only [successiveRelativeFrobenius, Over.comp_left]
    refine ⟨inferInstance, inferInstance, universalHomeomorphism_comp _ _ hu ?_⟩
    exact (finite_flat_universalHomeomorphism_of_isIso _).2.2
  | succ n ih =>
    let B := _root_.AlgebraicGeometry.nFoldFrobeniusTwist S p hS (n + 1) A
    have : Smooth B.hom := inferInstanceAs
      (Smooth (pullback.snd A.hom (absoluteFrobeniusPow S p hS (n + 1))))
    obtain ⟨hf, hl, hu⟩ := finite_flat_universalHomeomorphism_relativeFrobenius p hS B
    obtain ⟨hif, hil, hiu⟩ := ih
    simp only [successiveRelativeFrobenius, Over.comp_left]
    refine ⟨inferInstance, inferInstance, universalHomeomorphism_comp _ _ hiu ?_⟩
    exact universalHomeomorphism_comp _ _ hu
      (finite_flat_universalHomeomorphism_of_isIso _).2.2

/-- The original n-fold map is finite, flat and a universal homeomorphism on every smooth object. -/
theorem nFoldRelativeFrobenius_properties (n : ℕ) (X : SmoothSite S) :
    IsFinite (nFoldRelativeFrobenius p hS n X).left ∧
      Flat (nFoldRelativeFrobenius p hS n X).left ∧
      UniversalHomeomorphism (nFoldRelativeFrobenius p hS n X).left := by
  let A := (forget S).obj X
  have : Smooth A.hom := inferInstanceAs (Smooth X.hom)
  change IsFinite (_root_.AlgebraicGeometry.nFoldRelativeFrobenius S p hS n A).left ∧
    Flat (_root_.AlgebraicGeometry.nFoldRelativeFrobenius S p hS n A).left ∧
    UniversalHomeomorphism (_root_.AlgebraicGeometry.nFoldRelativeFrobenius S p hS n A).left
  cases n with
  | zero =>
    let r := (_root_.AlgebraicGeometry.nFoldRelativeFrobenius S p hS 0 A).left
    let t := pullback.fst A.hom (absoluteFrobeniusPow S p hS 0)
    have ht : IsIso t := by change IsIso (pullback.fst A.hom (𝟙 S)); infer_instance
    have hrt : r ≫ t = 𝟙 A.left := by
      simpa only [absoluteFrobeniusPow, pow_zero, End.one_asHom] using
        _root_.AlgebraicGeometry.nFoldRelativeFrobenius_fst S p hS 0 A
    have : IsIso (r ≫ t) := hrt ▸ inferInstance
    have : IsIso r := IsIso.of_isIso_comp_right r t
    exact finite_flat_universalHomeomorphism_of_isIso r
  | succ n =>
    rw [_root_.AlgebraicGeometry.nFoldRelativeFrobenius_eq_successiveRelativeFrobenius]
    exact finite_flat_universalHomeomorphism_successive p hS A n

instance (n : ℕ) (X : SmoothSite S) : IsFinite (nFoldRelativeFrobenius p hS n X).left :=
  (nFoldRelativeFrobenius_properties p hS n X).1

instance (n : ℕ) (X : SmoothSite S) : Flat (nFoldRelativeFrobenius p hS n X).left :=
  (nFoldRelativeFrobenius_properties p hS n X).2.1

instance (n : ℕ) (X : SmoothSite S) :
    UniversalHomeomorphism (nFoldRelativeFrobenius p hS n X).left :=
  (nFoldRelativeFrobenius_properties p hS n X).2.2

/-- Restrict the original native n-fold Frobenius base-change functor to smooth objects. -/
def nFoldFrobeniusTwistFunctor (n : ℕ) : SmoothSite S ⥤ SmoothSite S where
  obj X := nFoldFrobeniusTwist p hS n X
  map f := homMk
    (((Over.pullback (absoluteFrobeniusPow S p hS n)).map ((forget S).map f)).left)
    (((Over.pullback (absoluteFrobeniusPow S p hS n)).map ((forget S).map f)).w)
  map_id X := by
    apply MorphismProperty.Over.Hom.ext
    exact congrArg (fun f => f.left)
      ((Over.pullback (absoluteFrobeniusPow S p hS n)).map_id ((forget S).obj X))
  map_comp f g := by
    apply MorphismProperty.Over.Hom.ext
    exact congrArg (fun f => f.left)
      ((Over.pullback (absoluteFrobeniusPow S p hS n)).map_comp
        ((forget S).map f) ((forget S).map g))

/-- Naturality on the original smooth site is precisely the native n-fold map's square. -/
theorem nFoldRelativeFrobenius_naturality (n : ℕ) {X Y : SmoothSite S} (f : X ⟶ Y) :
    nFoldRelativeFrobenius p hS n X ≫ (nFoldFrobeniusTwistFunctor p hS n).map f =
      f ≫ nFoldRelativeFrobenius p hS n Y := by
  apply MorphismProperty.Over.Hom.ext
  exact congrArg (fun f => f.left)
    (nFoldRelativeFrobenius_comp_natural S p hS n ((forget S).map f))

/-- The original n-fold relative Frobenius as a natural transformation. -/
def nFoldRelativeFrobeniusNatTrans (n : ℕ) :
    𝟭 (SmoothSite S) ⟶ nFoldFrobeniusTwistFunctor p hS n where
  app X := nFoldRelativeFrobenius p hS n X
  naturality _ _ f := (nFoldRelativeFrobenius_naturality p hS n f).symm

end AlgebraicGeometry.Scheme.SmoothSite
