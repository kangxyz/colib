/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.IncidenceMaps

/-!
# The finite exterior-incidence square and the parameter diagonal

Write `I` for the full original incidence and `B = X × Z` for its target. The
map `I × T → B × T` is the literal base change of the original finite incidence
map. The map to `(X × T) × (Z × T)` then factors through the closed parameter
diagonal `B × T → (X × T) × (Z × T)`.

All objects are the original scheme-theoretic products. The incidence may be
nonreduced, reducible, disconnected or empty. Finiteness comes from the actual
incidence map and base change; no ambient projection is asserted to be proper.
The parameter-diagonal map is a section of a separated morphism, hence a closed
immersion. Its degree-one factor must not be confused with the unrestricted
residue degrees of the finite base-changed incidence map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u

namespace Stacks.Chow

variable {S : Scheme.{u}} (X Z T : SmoothSite S)

/-- The original outer product with one copy of the parameter. -/
abbrev exteriorOuterProduct : Scheme.{u} :=
  pullback (pullback.fst X.hom Z.hom ≫ X.hom) T.hom

/-- The parameter diagonal repeats the same parameter in the two outer factors. -/
def exteriorOuterDiagonal : exteriorOuterProduct X Z T ⟶
    pullback (SmoothSite.product X T).hom (SmoothSite.product Z T).hom :=
  pullback.lift
    (pullback.lift (pullback.fst _ _ ≫ pullback.fst X.hom Z.hom) (pullback.snd _ _)
      (by simpa only [Category.assoc] using
        (pullback.condition (f := pullback.fst X.hom Z.hom ≫ X.hom) (g := T.hom))))
    (pullback.lift (pullback.fst _ _ ≫ pullback.snd X.hom Z.hom) (pullback.snd _ _)
      (by simp only [Category.assoc, ← pullback.condition]))
    (by
      simp only [SmoothSite.product_hom]
      rw [pullback.lift_fst_assoc, pullback.lift_fst_assoc]
      simp only [Category.assoc, pullback.condition])

/-- Forget the second parameter, retaining both original outer coordinates. -/
def exteriorOuterRetraction :
    pullback (SmoothSite.product X T).hom (SmoothSite.product Z T).hom ⟶
      exteriorOuterProduct X Z T :=
  pullback.lift
    (pullback.lift
      (pullback.fst _ _ ≫ pullback.fst X.hom T.hom)
      (pullback.snd _ _ ≫ pullback.fst Z.hom T.hom)
      (by simpa only [SmoothSite.product_hom, Category.assoc] using
        (pullback.condition (f := (SmoothSite.product X T).hom)
          (g := (SmoothSite.product Z T).hom))))
    (pullback.fst _ _ ≫ pullback.snd X.hom T.hom)
    (by
      rw [pullback.lift_fst_assoc]
      simp only [Category.assoc, pullback.condition])

@[reassoc (attr := simp)]
theorem exteriorOuterDiagonal_retraction :
    exteriorOuterDiagonal X Z T ≫ exteriorOuterRetraction X Z T =
      𝟙 (exteriorOuterProduct X Z T) := by
  apply pullback.hom_ext
  · apply pullback.hom_ext <;>
      simp [exteriorOuterDiagonal, exteriorOuterRetraction, Category.assoc]
  · simp [exteriorOuterDiagonal, exteriorOuterRetraction, Category.assoc]

/-- The retraction is over the specified base; its separatedness follows from that
of its source, without imposing properness on any projection. -/
@[reassoc]
theorem exteriorOuterRetraction_base :
    exteriorOuterRetraction X Z T ≫
        (pullback.fst (pullback.fst X.hom Z.hom ≫ X.hom) T.hom ≫
          pullback.fst X.hom Z.hom ≫ X.hom) =
      (SmoothSite.product (SmoothSite.product X T) (SmoothSite.product Z T)).hom := by
  simp [exteriorOuterRetraction, SmoothSite.product_hom, Category.assoc]

instance exteriorOuterRetraction_isSeparated : IsSeparated (exteriorOuterRetraction X Z T) := by
  have : IsSeparated (exteriorOuterRetraction X Z T ≫
      (pullback.fst (pullback.fst X.hom Z.hom ≫ X.hom) T.hom ≫
        pullback.fst X.hom Z.hom ≫ X.hom)) := by
    rw [exteriorOuterRetraction_base]
    infer_instance
  exact IsSeparated.of_comp (exteriorOuterRetraction X Z T)
    (pullback.fst (pullback.fst X.hom Z.hom ≫ X.hom) T.hom ≫
      pullback.fst X.hom Z.hom ≫ X.hom)

/-- A section of a separated morphism is a closed immersion. Here the section is the
actual diagonal-parameter map, not the finite incidence map. -/
instance exteriorOuterDiagonal_isClosedImmersion :
    IsClosedImmersion (exteriorOuterDiagonal X Z T) := by
  have : IsClosedImmersion (exteriorOuterDiagonal X Z T ≫ exteriorOuterRetraction X Z T) := by
    rw [exteriorOuterDiagonal_retraction]
    infer_instance
  exact IsClosedImmersion.of_comp (exteriorOuterDiagonal X Z T)
    (exteriorOuterRetraction X Z T)

variable (Y : SmoothSite S)
  (z : pullback (C := Scheme) X.hom Y.hom)
  (w : pullback (C := Scheme) Y.hom Z.hom)

/-- The finite original incidence map with one unchanged parameter. -/
def exteriorIncidenceProductOuter : exteriorIncidenceProduct X Y Z T z w ⟶
    exteriorOuterProduct X Z T :=
  pullback.lift
    (pullback.fst _ _ ≫ correspondenceIncidenceMap X.hom Y.hom Z.hom z w)
    (pullback.snd _ _) (by
      rw [Category.assoc, correspondenceIncidenceMap_fst_assoc]
      exact pullback.condition
        (f := correspondenceIncidenceLeft X.hom Y.hom Z.hom z w ≫ X.hom) (g := T.hom))

@[reassoc (attr := simp)]
theorem exteriorIncidenceProductOuter_fst :
    exteriorIncidenceProductOuter X Z T Y z w ≫
        pullback.fst (pullback.fst X.hom Z.hom ≫ X.hom) T.hom =
      pullback.fst _ _ ≫ correspondenceIncidenceMap X.hom Y.hom Z.hom z w :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem exteriorIncidenceProductOuter_snd :
    exteriorIncidenceProductOuter X Z T Y z w ≫
        pullback.snd (pullback.fst X.hom Z.hom ≫ X.hom) T.hom =
      pullback.snd _ _ :=
  pullback.lift_snd _ _ _

/-- The full unreduced incidence product is the actual Cartesian base change of its
original source-target map. -/
theorem exteriorIncidenceProductOuter_isPullback :
    IsPullback
      (pullback.fst _ _ : exteriorIncidenceProduct X Y Z T z w ⟶
        correspondenceIncidence X.hom Y.hom Z.hom z w)
      (exteriorIncidenceProductOuter X Z T Y z w)
      (correspondenceIncidenceMap X.hom Y.hom Z.hom z w)
      (pullback.fst (pullback.fst X.hom Z.hom ≫ X.hom) T.hom) := by
  have hp : IsPullback
      (pullback.fst _ _ : exteriorIncidenceProduct X Y Z T z w ⟶
        correspondenceIncidence X.hom Y.hom Z.hom z w)
      (exteriorIncidenceProductOuter X Z T Y z w ≫
        pullback.snd (pullback.fst X.hom Z.hom ≫ X.hom) T.hom)
      (correspondenceIncidenceMap X.hom Y.hom Z.hom z w ≫
        (pullback.fst X.hom Z.hom ≫ X.hom)) T.hom := by
    simpa only [exteriorIncidenceProductOuter_snd, ← Category.assoc,
      correspondenceIncidenceMap_fst] using
      (IsPullback.of_hasPullback
        (correspondenceIncidenceLeft X.hom Y.hom Z.hom z w ≫ X.hom) T.hom)
  exact hp.of_bot (exteriorIncidenceProductOuter_fst X Z T Y z w).symm
    (IsPullback.of_hasPullback (pullback.fst X.hom Z.hom ≫ X.hom) T.hom)

/-- Finiteness is inherited from the actual original finite support map. -/
theorem exteriorIncidenceProductOuter_isFinite
    (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
    (hw : IsFiniteCorrespondencePoint Y.hom Z.hom w) :
    IsFinite (exteriorIncidenceProductOuter X Z T Y z w) := by
  let := isFinite_correspondenceIncidenceMap X.hom Y.hom Z.hom z w hz hw
  exact MorphismProperty.of_isPullback
    (exteriorIncidenceProductOuter_isPullback X Z T Y z w) inferInstance

end Stacks.Chow

namespace Stacks.Chow

variable {k : Type u} [Field k] (X Y Z T : SmoothSite (Spec (.of k)))
  (z : pullback (C := Scheme) X.hom Y.hom)
  (w : pullback (C := Scheme) Y.hom Z.hom)

/-- The actual full-product outer map factors through the common parameter diagonal. -/
@[reassoc]
theorem exteriorIncidenceProductOuter_diagonal :
    exteriorIncidenceProductOuter X Z T Y z w ≫ exteriorOuterDiagonal X Z T =
      exteriorIncidenceProductMap X Y Z T z w := by
  apply pullback.hom_ext
  · rw [Category.assoc, exteriorOuterDiagonal, pullback.lift_fst,
      exteriorIncidenceProductMap, pullback.lift_fst]
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc,
        exteriorIncidenceProductOuter_fst, Category.assoc, correspondenceIncidenceMap_fst]
      exact (exteriorIncidenceProductSource_fst X Y Z T z w).symm
    · rw [Category.assoc, pullback.lift_snd, exteriorIncidenceProductOuter_snd]
      exact (exteriorIncidenceProductSource_snd X Y Z T z w).symm
  · rw [Category.assoc, exteriorOuterDiagonal, pullback.lift_snd,
      exteriorIncidenceProductMap, pullback.lift_snd]
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc,
        exteriorIncidenceProductOuter_fst, Category.assoc, correspondenceIncidenceMap_snd]
      exact (exteriorIncidenceProductTarget_fst X Y Z T z w).symm
    · rw [Category.assoc, pullback.lift_snd, exteriorIncidenceProductOuter_snd]
      exact (exteriorIncidenceProductTarget_snd X Y Z T z w).symm

end Stacks.Chow
