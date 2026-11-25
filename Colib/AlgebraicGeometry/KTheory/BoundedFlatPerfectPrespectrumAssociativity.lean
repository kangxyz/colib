/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectNormalizedPullbackAssociativity
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumUnitRoutes
public import Colib.KTheory.Waldhausen.Iterated.NormalizationPasting
public import Colib.Topology.Prespectrum.RelativeHomotopyHorizontal
public import Colib.Topology.Prespectrum.RelativeHomotopyWhiskering

/-! # Whole associativity of the actual split bounded-flat pullback tracks

The two original triple routes concatenate the actual geometric and chosen-zero binary
composition tracks. The relative comparison is the original transformation pasting of
the proved normalized geometric equation, joined to the existing binary triangles.
No track is replaced by equality, and the scheme and prespectrum transports are explicit.

Implementation provenance: Quillen `BoundedFlat/NormalizedPullbackCoherence.lean:104-133`
and `BoundedFlat/TripleTrack.lean:23-175` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry AlgebraicGeometry.RingedSpace Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules

local notation "K" => boundedAboveFlatPerfectPullbackPrespectrumMap
local notation "N" => boundedAboveFlatPerfectNormalizedPullback
local notation "NComp" => boundedAboveFlatPerfectNormalizedPullbackCompIso
local notation "hN" => boundedAboveFlatPerfectNormalizedPullback_exact
local notation "zN" => boundedAboveFlatPerfectNormalizedPullback_obj_zero
local notation "normTrack" => boundedAboveFlatPerfectNormalizedCompTrack
local notation "splitTrack" => boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy

/-- First decompose the last two maps and postcompose the whole split comparison. -/
def boundedAboveFlatPerfectTripleLeftTrack {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    Homotopy (K (f ≫ g ≫ h)) ((K h ≫ K g) ≫ K f) :=
  (splitTrack f (g ≫ h)).trans ((splitTrack g h).postcomp (K f))

/-- First decompose the first two maps, retaining both associativity transports. -/
def boundedAboveFlatPerfectTripleRightTrack {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    Homotopy (K (f ≫ g ≫ h)) ((K h ≫ K g) ≫ K f) :=
  ((splitTrack (f ≫ g) h).trans (Homotopy.precomp (K h) (splitTrack f g))).cast
    (congrArg K (Category.assoc f g h)) (Category.assoc _ _ _).symm

/-- The left triple route using the chosen-zero transformation tracks. -/
def boundedAboveFlatPerfectNormalizedTripleLeftTrack {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    Homotopy (K (f ≫ g ≫ h)) ((K h ≫ K g) ≫ K f) :=
  (normTrack f (g ≫ h)).trans ((normTrack g h).postcomp (K f))

/-- The right chosen-zero triple route with both associativity transports. -/
def boundedAboveFlatPerfectNormalizedTripleRightTrack {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    Homotopy (K (f ≫ g ≫ h)) ((K h ≫ K g) ≫ K f) :=
  ((normTrack (f ≫ g) h).trans (Homotopy.precomp (K h) (normTrack f g))).cast
    (congrArg K (Category.assoc f g h)) (Category.assoc _ _ _).symm

/-- Endpoint casts leave the entire original normalized transformation track unchanged. -/
theorem boundedAboveFlatPerfectNormalizedCompTrack_level {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    (normTrack f g).level n =
      (originalPrespectrumTransformationHomotopy
        (boundedAboveFlatPerfectWaldhausen Z.toRingedSpace)
        (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
        (hN (f ≫ g)) ((hN g).comp (hN f))
        (zN (f ≫ g)) ((congrArg (N f).obj (zN g)).trans (zN f))
        (NComp f g).hom
        (fun _ ↦ (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq_iso _
          inferInstance)).level n := rfl

set_option maxHeartbeats 900000 in
-- Elaborating these triangles compares exact pullbacks across four composite functors.
/-- The two normalized triangles realize the four exact pullback transformations. -/
def boundedAboveFlatPerfectNormalizedTriplePasting {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :=
  let W := boundedAboveFlatPerfectWaldhausen T.toRingedSpace
  let U := boundedAboveFlatPerfectWaldhausen X.toRingedSpace
  originalPrespectrumPastingHomotopy W U
    (hN (f ≫ g ≫ h))
    ((hN (g ≫ h)).comp (hN f))
    ((hN h).comp (hN (f ≫ g)))
    ((hN h).comp ((hN g).comp (hN f)))
    (zN (f ≫ g ≫ h))
    ((congrArg (N f).obj (zN (g ≫ h))).trans (zN f))
    ((congrArg (N (f ≫ g)).obj (zN h)).trans (zN (f ≫ g)))
    ((congrArg (N f).obj ((congrArg (N g).obj (zN h)).trans (zN g))).trans (zN f))
    (NComp f (g ≫ h)).hom
    (whiskerRight (NComp g h).hom (N f) ≫ (Functor.associator (N h) (N g) (N f)).hom)
    (eqToHom (congrArg N (Category.assoc f g h).symm) ≫ (NComp (f ≫ g) h).hom)
    (whiskerLeft (N h) (NComp f g).hom)
    (fun _ ↦ U.weq_iso _ inferInstance)
    (fun _ ↦ U.weq_iso _ inferInstance)
    (fun _ ↦ U.weq_iso _ inferInstance)
    (fun _ ↦ U.weq_iso _ inferInstance)
    (boundedAboveFlatPerfectNormalizedPullbackCompIso_two_routes f g h)

set_option maxHeartbeats 1200000 in
-- The level comparisons unfold the chosen-zero prespectrum maps and the associativity casts.
/-- The normalized triple routes agree relatively, with their entire realized paths retained. -/
def boundedAboveFlatPerfectNormalizedTripleTrackComparison {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (boundedAboveFlatPerfectNormalizedTripleLeftTrack f g h).RelHomotopy
      (boundedAboveFlatPerfectNormalizedTripleRightTrack f g h) := by
  let W := boundedAboveFlatPerfectWaldhausen T.toRingedSpace
  let U := boundedAboveFlatPerfectWaldhausen X.toRingedSpace
  let V := boundedAboveFlatPerfectWaldhausen Y.toRingedSpace
  have J := boundedAboveFlatPerfectNormalizedTriplePasting f g h
  refine J.ofLevels _ _ ?_ ?_
  · intro n
    apply Homotopy.trans_level_congr
    · exact boundedAboveFlatPerfectNormalizedCompTrack_level f (g ≫ h) n
    · have he := originalPrespectrumTransformationHomotopy_postcomp_level
        (hN (g ≫ h)) ((hN h).comp (hN g)) (hN f)
        (zN (g ≫ h)) ((congrArg (N g).obj (zN h)).trans (zN g)) (zN f)
        (NComp g h).hom (fun _ ↦ V.weq_iso _ inferInstance) n
      refine (Homotopy.postcomp_level_congr _ _ _ n
        (boundedAboveFlatPerfectNormalizedCompTrack_level g h n)).trans
        (he.symm.trans ?_)
      apply originalPrespectrumTransformationHomotopy_congr_level W U _ _ _ _ _ _ _ _ rfl rfl
      have hAssoc : whiskerRight (NComp g h).hom (N f) =
          whiskerRight (NComp g h).hom (N f) ≫
            (Functor.associator (N h) (N g) (N f)).hom := by
        apply NatTrans.ext
        funext A
        simp only [NatTrans.comp_app, associator_hom_app, Category.comp_id]
      simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using hAssoc
  · intro n
    unfold boundedAboveFlatPerfectNormalizedTripleRightTrack
    rw [Homotopy.cast_level]
    apply Homotopy.trans_level_congr
    · rw [boundedAboveFlatPerfectNormalizedCompTrack_level]
      apply originalPrespectrumTransformationHomotopy_congr_level W U _ _ _ _ _ _ _ _
        (congrArg N (Category.assoc f g h)) rfl
      simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
    · have he := originalPrespectrumTransformationHomotopy_precomp_level
        (hN h) (hN (f ≫ g)) ((hN g).comp (hN f))
        (zN h) (zN (f ≫ g)) ((congrArg (N f).obj (zN g)).trans (zN f))
        (NComp f g).hom (fun _ ↦ U.weq_iso _ inferInstance) n
      exact (Homotopy.precomp_level_congr _ _ _ n
        (boundedAboveFlatPerfectNormalizedCompTrack_level f g n)).trans he.symm

/-- The whole relative associativity of the original split geometric pullback tracks. -/
def boundedAboveFlatPerfectTripleTrackComparison {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (boundedAboveFlatPerfectTripleLeftTrack f g h).RelHomotopy
      (boundedAboveFlatPerfectTripleRightTrack f g h) :=
  ((boundedAboveFlatPerfectNormalizedCompTrackComparison f (g ≫ h)).hcomp
    ((boundedAboveFlatPerfectNormalizedCompTrackComparison g h).postcomp (K f))).symm.trans
    ((boundedAboveFlatPerfectNormalizedTripleTrackComparison f g h).trans
      (((boundedAboveFlatPerfectNormalizedCompTrackComparison (f ≫ g) h).hcomp
        (Homotopy.RelHomotopy.precomp (K h)
          (boundedAboveFlatPerfectNormalizedCompTrackComparison f g))).cast
        (congrArg K (Category.assoc f g h)) (Category.assoc _ _ _).symm))

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TripleTrack.lean:139-175"
  "adaptation" "Whole associativity retaining the original split tracks and endpoint transports."]
  boundedAboveFlatPerfectTripleTrackComparison

end AlgebraicGeometry.Scheme.Modules
