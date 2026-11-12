/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodBaseChange
public import Mathlib.AlgebraicGeometry.AffineSpace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPoint

/-!
# The split maps for affine-space henselian induction

Affine space has its rational origin marked by the native algebraic closure of the base field.
Dropping the first coordinate and inserting a zero first coordinate preserve these markings.
Their pullbacks act on the original marked affine étale neighborhood values, in universe `u + 1`.
The composite from dimension `d` to dimension `d + 1` and back is the identity. The reverse
composite, which requires the representative-specific curve rigidity argument, is not asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable (k : Type u) [Field k]

/-- Native affine space as an original smooth separated finite-type object. -/
abbrev affineSpaceObject (d : ℕ) : SmoothSite (Spec (.of k)) :=
  mk (AffineSpace (ULift.{u} (Fin d)) (Spec (.of k)) ↘ Spec (.of k))

instance (d : ℕ) : IsAffine (affineSpaceObject k d).left :=
  inferInstanceAs (IsAffine (AffineSpace (ULift.{u} (Fin d)) (Spec (.of k))))

/-- The rational origin of the native affine space. -/
def affineSpaceOrigin (d : ℕ) :
    Spec (.of k) ⟶ AffineSpace (ULift.{u} (Fin d)) (Spec (.of k)) :=
  AffineSpace.homOfVector (𝟙 _) (fun _ ↦ 0)

/-- The native algebraically closed marking above the rational origin. -/
def affineSpaceOriginGeometricPoint (d : ℕ) : GeometricPoint (affineSpaceObject k d).left where
  residueField := AlgebraicClosure k
  hom := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))) ≫ affineSpaceOrigin k d

/-- Coordinate projection dropping the first coordinate. -/
def affineSpaceCoordinateProjection (d : ℕ) :
    affineSpaceObject k (d + 1) ⟶ affineSpaceObject k d :=
  homMk (AffineSpace.reindex (fun i : ULift.{u} (Fin d) ↦ (⟨i.down.succ⟩ :
    ULift.{u} (Fin (d + 1)))) (Spec (.of k))) (by
      exact AffineSpace.reindex_over _ _)

/-- Zero-section inserting a zero first coordinate. -/
def affineSpaceCoordinateZeroSection (d : ℕ) :
    affineSpaceObject k d ⟶ affineSpaceObject k (d + 1) :=
  homMk (AffineSpace.homOfVector (affineSpaceObject k d).hom
    (fun i : ULift.{u} (Fin (d + 1)) ↦ Fin.cases 0
      (fun j ↦ AffineSpace.coord (Spec (.of k)) (⟨j⟩ : ULift.{u} (Fin d))) i.down))
    (AffineSpace.homOfVector_over _ _)

theorem affineSpaceCoordinateProjection_left (d : ℕ) :
    (affineSpaceCoordinateProjection k d).left =
      AffineSpace.reindex (fun i : ULift.{u} (Fin d) ↦
        (⟨i.down.succ⟩ : ULift.{u} (Fin (d + 1)))) (Spec (.of k)) := rfl

theorem affineSpaceCoordinateZeroSection_left (d : ℕ) :
    (affineSpaceCoordinateZeroSection k d).left =
      AffineSpace.homOfVector (AffineSpace (ULift.{u} (Fin d)) (Spec (.of k)) ↘ Spec (.of k))
        (fun i : ULift.{u} (Fin (d + 1)) ↦ Fin.cases 0
          (fun j ↦ AffineSpace.coord (Spec (.of k)) (⟨j⟩ : ULift.{u} (Fin d))) i.down) := rfl

@[reassoc (attr := simp)]
theorem affineSpaceCoordinateZeroSection_projection (d : ℕ) :
    affineSpaceCoordinateZeroSection k d ≫ affineSpaceCoordinateProjection k d = 𝟙 _ := by
  apply MorphismProperty.Over.Hom.ext
  change AffineSpace.homOfVector
    (AffineSpace (ULift.{u} (Fin d)) (Spec (.of k)) ↘ Spec (.of k))
      (fun i : ULift.{u} (Fin (d + 1)) ↦ Fin.cases 0
        (fun j ↦ AffineSpace.coord (Spec (.of k)) (⟨j⟩ : ULift.{u} (Fin d))) i.down) ≫
    AffineSpace.reindex (fun i : ULift.{u} (Fin d) ↦
      (⟨i.down.succ⟩ : ULift.{u} (Fin (d + 1)))) (Spec (.of k)) =
        𝟙 (AffineSpace (ULift.{u} (Fin d)) (Spec (.of k)))
  apply AffineSpace.hom_ext
  · simp only [Category.assoc, AffineSpace.reindex_over, AffineSpace.homOfVector_over,
      Category.id_comp]
  · intro i
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AffineSpace.reindex_appTop_coord, AffineSpace.homOfVector_appTop_coord,
      Scheme.Hom.id_appTop, CommRingCat.id_apply, Fin.cases_succ]

@[reassoc (attr := simp)]
theorem affineSpaceOrigin_projection (d : ℕ) :
    affineSpaceOrigin k (d + 1) ≫ (affineSpaceCoordinateProjection k d).left =
      affineSpaceOrigin k d := by
  change affineSpaceOrigin k (d + 1) ≫
    AffineSpace.reindex (fun i : ULift.{u} (Fin d) ↦
      (⟨i.down.succ⟩ : ULift.{u} (Fin (d + 1)))) (Spec (.of k)) = affineSpaceOrigin k d
  apply AffineSpace.hom_ext
  · simp [affineSpaceOrigin, Category.assoc]
  · intro i
    simp only [affineSpaceOrigin, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AffineSpace.reindex_appTop_coord, AffineSpace.homOfVector_appTop_coord]

@[reassoc (attr := simp)]
theorem affineSpaceOrigin_zeroSection (d : ℕ) :
    affineSpaceOrigin k d ≫ (affineSpaceCoordinateZeroSection k d).left =
      affineSpaceOrigin k (d + 1) := by
  change affineSpaceOrigin k d ≫
    AffineSpace.homOfVector (AffineSpace (ULift.{u} (Fin d)) (Spec (.of k)) ↘ Spec (.of k))
      (fun i : ULift.{u} (Fin (d + 1)) ↦ Fin.cases 0
        (fun j ↦ AffineSpace.coord (Spec (.of k)) (⟨j⟩ : ULift.{u} (Fin d))) i.down) =
          affineSpaceOrigin k (d + 1)
  apply AffineSpace.hom_ext
  · simp [affineSpaceOrigin, Category.assoc]
  · intro i
    rcases i with ⟨i⟩
    refine Fin.cases ?_ (fun j ↦ ?_) i <;>
      simp only [affineSpaceOrigin, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        AffineSpace.homOfVector_appTop_coord, Fin.cases_zero, Fin.cases_succ, map_zero]

@[reassoc (attr := simp)]
theorem affineSpaceOriginGeometricPoint_projection (d : ℕ) :
    (affineSpaceOriginGeometricPoint k (d + 1)).hom ≫
      (affineSpaceCoordinateProjection k d).left = (affineSpaceOriginGeometricPoint k d).hom := by
  exact (Category.assoc _ _ _).trans
    (congrArg (fun q ↦ Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))) ≫ q)
      (affineSpaceOrigin_projection k d))

@[reassoc (attr := simp)]
theorem affineSpaceOriginGeometricPoint_zeroSection (d : ℕ) :
    (affineSpaceOriginGeometricPoint k d).hom ≫
      (affineSpaceCoordinateZeroSection k d).left =
        (affineSpaceOriginGeometricPoint k (d + 1)).hom := by
  exact (Category.assoc _ _ _).trans
    (congrArg (fun q ↦ Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))) ≫ q)
      (affineSpaceOrigin_zeroSection k d))

/-- The original neighborhood value at the algebraically closed marking of the rational origin. -/
abbrev affineSpaceOriginValue (d : ℕ)
    (F : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
  etaleNeighborhoodValue (affineSpaceObject k d) (affineSpaceOriginGeometricPoint k d).hom F

/-- Pullback along the coordinate projection on the original neighborhood values. -/
@[colib_tag "COL-1093"]
def affineSpaceOriginProjectionPullback (d : ℕ)
    (F : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    affineSpaceOriginValue k d F ⟶ affineSpaceOriginValue k (d + 1) F :=
  etaleNeighborhoodValuePullback (affineSpaceCoordinateProjection k d)
    (affineSpaceOriginGeometricPoint_projection k d) F

/-- Pullback along the zero-section on the original neighborhood values. -/
@[colib_tag "COL-1093"]
def affineSpaceOriginZeroSectionPullback (d : ℕ)
    (F : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    affineSpaceOriginValue k (d + 1) F ⟶ affineSpaceOriginValue k d F :=
  etaleNeighborhoodValuePullback (affineSpaceCoordinateZeroSection k d)
    (affineSpaceOriginGeometricPoint_zeroSection k d) F

/-- The projection pullback on each original affine étale representative. -/
theorem affineSpaceOriginProjectionPullback_representative (d : ℕ)
    (F : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (B : EtaleNeighborhood (affineSpaceObject k d) (affineSpaceOriginGeometricPoint k d).hom)
    (b : F.obj (op ((etaleNeighborhoodToSmooth (affineSpaceObject k d)
      (affineSpaceOriginGeometricPoint k d).hom).obj B))) :
    affineSpaceOriginProjectionPullback k d F
        (toEtaleNeighborhoodValue (affineSpaceObject k d)
          (affineSpaceOriginGeometricPoint k d).hom B F b) =
      toEtaleNeighborhoodValue (affineSpaceObject k (d + 1))
        (affineSpaceOriginGeometricPoint k (d + 1)).hom
        (etaleNeighborhoodPullback (affineSpaceCoordinateProjection k d)
          (affineSpaceOriginGeometricPoint_projection k d) B) F
        (F.map (etaleNeighborhoodPullbackHom (affineSpaceCoordinateProjection k d)
          (affineSpaceOriginGeometricPoint_projection k d) B).op b) :=
  ConcreteCategory.congr_hom
    (toEtaleNeighborhoodValue_pullback (affineSpaceCoordinateProjection k d)
      (affineSpaceOriginGeometricPoint_projection k d) F B) b

/-- The zero-section pullback on each original affine étale representative. -/
theorem affineSpaceOriginZeroSectionPullback_representative (d : ℕ)
    (F : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (B : EtaleNeighborhood (affineSpaceObject k (d + 1))
      (affineSpaceOriginGeometricPoint k (d + 1)).hom)
    (b : F.obj (op ((etaleNeighborhoodToSmooth (affineSpaceObject k (d + 1))
      (affineSpaceOriginGeometricPoint k (d + 1)).hom).obj B))) :
    affineSpaceOriginZeroSectionPullback k d F
        (toEtaleNeighborhoodValue (affineSpaceObject k (d + 1))
          (affineSpaceOriginGeometricPoint k (d + 1)).hom B F b) =
      toEtaleNeighborhoodValue (affineSpaceObject k d)
        (affineSpaceOriginGeometricPoint k d).hom
        (etaleNeighborhoodPullback (affineSpaceCoordinateZeroSection k d)
          (affineSpaceOriginGeometricPoint_zeroSection k d) B) F
        (F.map (etaleNeighborhoodPullbackHom (affineSpaceCoordinateZeroSection k d)
          (affineSpaceOriginGeometricPoint_zeroSection k d) B).op b) :=
  ConcreteCategory.congr_hom
    (toEtaleNeighborhoodValue_pullback (affineSpaceCoordinateZeroSection k d)
      (affineSpaceOriginGeometricPoint_zeroSection k d) F B) b

/-- The normalized split composite, without assuming the reverse rigidity composite. -/
@[colib_tag "COL-1093", reassoc (attr := simp)]
theorem affineSpaceOriginProjectionPullback_zeroSection (d : ℕ)
    (F : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    affineSpaceOriginProjectionPullback k d F ≫ affineSpaceOriginZeroSectionPullback k d F = 𝟙 _ :=
  etaleNeighborhoodValuePullback_retraction _ _ _ _
    (affineSpaceCoordinateZeroSection_projection k d) F

end AlgebraicGeometry.Scheme.SmoothSite
