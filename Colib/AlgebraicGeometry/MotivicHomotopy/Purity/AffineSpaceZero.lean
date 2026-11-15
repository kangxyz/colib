/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.PositiveRankSurjectivity
public import Colib.AlgebraicGeometry.Sites.Smooth.Basic

/-! # The original zero point in a tower of affine spaces -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AffineSpace

universe u

namespace AlgebraicGeometry.AffineSpace

variable (S : Scheme.{u})

/-- The section given by the zero value on every standard coordinate. -/
abbrev origin (n : Type u) : S ⟶ AffineSpace n S := homOfVector (𝟙 S) (fun _ => 0)

@[reassoc]
theorem origin_over (n : Type u) : origin S n ≫ (AffineSpace n S ↘ S) = 𝟙 S :=
  homOfVector_over _ _

instance origin_isClosedImmersion (n : Type u) : IsClosedImmersion (origin S n) := by
  let p := AffineSpace n S ↘ S
  let : IsClosedImmersion (origin S n ≫ p) := by
    change IsClosedImmersion (origin S n ≫ (AffineSpace n S ↘ S))
    rw [origin_over]
    infer_instance
  exact IsClosedImmersion.of_comp (origin S n) p

theorem origin_appTop_coord (n : Type u) (i : n) :
    (origin S n).appTop (coord S i) = 0 := homOfVector_appTop_coord _ _ _

/-- The original marked origins commute with the affine-space base-change maps. -/
@[reassoc]
theorem origin_map {T : Scheme.{u}} (f : S ⟶ T) (n : Type u) :
    origin S n ≫ map n f = f ≫ origin T n := by
  apply hom_ext
  · calc
      _ = f := by simp only [Category.assoc, map_over, origin_over_assoc]
      _ = _ := by simp only [Category.assoc, origin_over, Category.comp_id]
  · intro j
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      map_appTop_coord, origin_appTop_coord, map_zero]

/-- The marked origins form the Cartesian zero-section square. -/
theorem isPullback_origin_map {T : Scheme.{u}} (f : S ⟶ T) (n : Type u) :
    IsPullback (origin S n) f (map n f) (origin T n) := by
  apply IsPullback.of_right (h₁₂ := (AffineSpace n S ↘ S))
    (h₂₂ := (AffineSpace n T ↘ T))
  · rw [origin_over, origin_over]
    exact IsPullback.of_id_fst
  · exact origin_map S f n
  · exact (isPullback_map (n := n) f).flip

/-- Reindexing the original coordinates preserves the marked origin. -/
@[reassoc]
theorem origin_reindex {n m : Type u} (i : m → n) :
    origin S n ≫ reindex i S = origin S m := by
  apply hom_ext
  · rw [Category.assoc, reindex_over, origin_over, origin_over]
  · intro j
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, reindex_appTop_coord,
      origin_appTop_coord, origin_appTop_coord]

/-- The original splitting of an affine space with two groups of coordinates
takes its zero section to the two successive zero sections. -/
@[reassoc]
theorem origin_affineSpaceSumIso (n m : Type u) :
    origin S (n ⊕ m) ≫ (Stacks.Chow.affineSpaceSumIso n m S).hom =
      origin S m ≫ origin (AffineSpace m S) n := by
  apply hom_ext
  · rw [Category.assoc, Stacks.Chow.affineSpaceSumIso_hom_over,
      origin_reindex, Category.assoc, origin_over, Category.comp_id]
  · intro i
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    change (origin S (n ⊕ m)).appTop
        ((homOfVector (reindex Sum.inr S) (fun j : n => coord S (Sum.inl j))).appTop
          (coord (AffineSpace m S) i)) =
      (origin S m).appTop ((origin (AffineSpace m S) n).appTop (coord (AffineSpace m S) i))
    rw [homOfVector_appTop_coord, origin_appTop_coord, origin_appTop_coord, map_zero]

/-- The literal affine line may be taken as the last coordinate of the tower,
preserving the section with all coordinates zero. -/
@[reassoc]
theorem origin_affineSpaceSuccLastIso (r : ℕ) :
    origin S (ULift.{u} (Fin (r + 1))) ≫
        (Stacks.Chow.affineSpaceReindexIso
          ((Stacks.Chow.uliftFinSuccSumEquiv.{u} r).trans (Equiv.sumComm _ _)) S ≪≫
          Stacks.Chow.affineSpaceSumIso (ULift.{u} (Fin 1)) (ULift.{u} (Fin r)) S).hom =
      origin S (ULift.{u} (Fin r)) ≫
        origin (AffineSpace (ULift.{u} (Fin r)) S) (ULift.{u} (Fin 1)) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (Stacks.Chow.affineSpaceSumIso _ _ S).hom)
      (origin_reindex S _)).trans (origin_affineSpaceSumIso S _ _))

/-- The projection of the last-coordinate tower is the original structure map. -/
theorem affineSpaceSuccLastIso_hom_over (r : ℕ) :
    (Stacks.Chow.affineSpaceReindexIso
      ((Stacks.Chow.uliftFinSuccSumEquiv.{u} r).trans (Equiv.sumComm _ _)) S ≪≫
      Stacks.Chow.affineSpaceSumIso (ULift.{u} (Fin 1)) (ULift.{u} (Fin r)) S).hom ≫
      ((AffineSpace (ULift.{u} (Fin 1)) (AffineSpace (ULift.{u} (Fin r)) S) ↘
        AffineSpace (ULift.{u} (Fin r)) S) ≫ (AffineSpace (ULift.{u} (Fin r)) S ↘ S)) =
      AffineSpace (ULift.{u} (Fin (r + 1))) S ↘ S := by
  rw [Iso.trans_hom, Category.assoc, ← Category.assoc
      (Stacks.Chow.affineSpaceSumIso (ULift.{u} (Fin 1)) (ULift.{u} (Fin r)) S).hom,
    Stacks.Chow.affineSpaceSumIso_hom_over, reindex_over,
    Stacks.Chow.affineSpaceReindexIso_hom_over]

end AlgebraicGeometry.AffineSpace

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}}

/-- The native affine scheme over a smooth base, regarded in the original smooth site. -/
def relativeAffineSpace (X : SmoothSite S) (n : ℕ) : SmoothSite S :=
  mk ((AffineSpace (ULift.{u} (Fin n)) X.left ↘ X.left) ≫ X.hom)

/-- The native zero section regarded as a map in the original smooth site. -/
def relativeAffineSpaceZeroSection (X : SmoothSite S) (n : ℕ) : X ⟶ relativeAffineSpace X n :=
  homMk (AffineSpace.origin X.left (ULift.{u} (Fin n))) (by
    dsimp [relativeAffineSpace]
    rw [← Category.assoc, AffineSpace.origin_over, Category.id_comp])

instance affineSpaceOrigin_isClosedImmersion (X : SmoothSite S) (n : ℕ) :
    IsClosedImmersion (relativeAffineSpaceZeroSection X n).left :=
  inferInstanceAs (IsClosedImmersion (AffineSpace.origin X.left (ULift.{u} (Fin n))))

/-- The original map of affine spaces over a map of smooth base schemes. -/
def affineSpaceObjectMap {X Y : SmoothSite S} (f : X ⟶ Y) (n : ℕ) :
    relativeAffineSpace X n ⟶ relativeAffineSpace Y n :=
  homMk (AffineSpace.map (ULift.{u} (Fin n)) f.left) (by
    change AffineSpace.map (ULift.{u} (Fin n)) f.left ≫ (_ ≫ Y.hom) = _
    rw [AffineSpace.map_over_assoc, MorphismProperty.Over.w f]
    rfl)

/-- The original zero sections give a map of supported affine spaces. -/
theorem affineSpaceOrigin_isPullback {X Y : SmoothSite S} (f : X ⟶ Y) (n : ℕ) :
    IsPullback (relativeAffineSpaceZeroSection X n).left f.left (affineSpaceObjectMap f n).left
      (relativeAffineSpaceZeroSection Y n).left :=
  AffineSpace.isPullback_origin_map X.left f.left _

end AlgebraicGeometry.Scheme.SmoothSite
