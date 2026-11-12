/-
Copyright (c) 2026 Colib contributors and AxiomMath/Stacks contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.Iterated

/-!
# Naturality of the original iterated Frobenius maps

These lower geometric proofs retain the native Frobenius powers, native pullbacks and maps.
They extract only naturality from the cited higher native modules, with no cohomology input.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Frobenius

universe u

namespace AlgebraicGeometry

/-- Naturality of the actual power of absolute Frobenius. -/
@[colib_ref "axiom_stacks_5ed82d14"
  "StacksFrontier/AlgebraicGeometry/Curves/InseparableFrobeniusIteration.lean:163-175"
  "adaptation" "lower extraction of naturality of the native absolute Frobenius power"]
theorem absoluteFrobeniusPow_comp_natural {X Y : Scheme.{u}} (f : X ⟶ Y)
    (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p)
    (n : ℕ) : absoluteFrobeniusPow X p hX n ≫ f = f ≫ absoluteFrobeniusPow Y p hY n := by
  induction n with
  | zero => simp [absoluteFrobeniusPow]
  | succ n ih =>
    simp only [absoluteFrobeniusPow, pow_succ, End.mul_asHom]
    change (absoluteFrobenius X p hX ≫ absoluteFrobeniusPow X p hX n) ≫ f =
      f ≫ (absoluteFrobenius Y p hY ≫ absoluteFrobeniusPow Y p hY n)
    rw [Category.assoc, ih, ← Category.assoc, absoluteFrobenius_naturality, Category.assoc]

/-- On an affine spectrum the actual iterated absolute Frobenius is the native ring power map. -/
theorem absoluteFrobeniusPow_spec (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    [CharP R p] (n : ℕ) :
    absoluteFrobeniusPow (Spec (.of R)) p (isInCharacteristic_spec R p) n =
      Spec.map (CommRingCat.ofHom (_root_.iterateFrobenius R p n)) := by
  apply ext_of_isAffine
  apply (cancel_mono (Scheme.ΓSpecIso (.of R)).hom).mp
  rw [Scheme.ΓSpecIso_naturality]
  ext a
  change (Scheme.ΓSpecIso (.of R)).hom
      ((absoluteFrobeniusPow (Spec (.of R)) p (isInCharacteristic_spec R p) n).appTop a) =
    _root_.iterateFrobenius R p n ((Scheme.ΓSpecIso (.of R)).hom a)
  rw [absoluteFrobenius_pow_appTop_apply, map_pow, iterateFrobenius_def]

/-- The native n-fold relative Frobenius is natural for the native n-fold pullback functor. -/
@[colib_ref "axiom_stacks_5ed82d14"
  "StacksFrontier/AlgebraicGeometry/EtaleCohomology/Trace/FrobeniusDescent.lean:70-104"
  "adaptation" "lower extraction of the actual n-fold Frobenius naturality square"]
theorem nFoldRelativeFrobenius_comp_natural (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) (n : ℕ) {X Y : Over S} (f : X ⟶ Y) :
    nFoldRelativeFrobenius S p hS n X ≫
        (Over.pullback (absoluteFrobeniusPow S p hS n)).map f =
      f ≫ nFoldRelativeFrobenius S p hS n Y := by
  ext
  apply pullback.hom_ext
  · have hlift : ((CategoryTheory.Over.pullback (absoluteFrobeniusPow S p hS n)).map f).left ≫
        pullback.fst Y.hom (absoluteFrobeniusPow S p hS n) =
          pullback.fst X.hom (absoluteFrobeniusPow S p hS n) ≫ f.left :=
      pullback.lift_fst _ _ _
    rw [CategoryTheory.Over.comp_left, Category.assoc, hlift, ← Category.assoc,
      nFoldRelativeFrobenius_fst, CategoryTheory.Over.comp_left, Category.assoc,
      nFoldRelativeFrobenius_fst]
    exact absoluteFrobeniusPow_comp_natural f.left p _ _ n
  · have hlift : ((CategoryTheory.Over.pullback (absoluteFrobeniusPow S p hS n)).map f).left ≫
        pullback.snd Y.hom (absoluteFrobeniusPow S p hS n) =
          pullback.snd X.hom (absoluteFrobeniusPow S p hS n) :=
      pullback.lift_snd _ _ _
    rw [CategoryTheory.Over.comp_left, Category.assoc, hlift, CategoryTheory.Over.comp_left,
      Category.assoc, nFoldRelativeFrobenius_snd, nFoldRelativeFrobenius_snd,
      CategoryTheory.Over.w]

end AlgebraicGeometry
