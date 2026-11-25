/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumUnitTracks
public import Colib.KTheory.Waldhausen.Iterated.NormalizationPasting
public import Colib.Topology.Prespectrum.RelativeHomotopyHorizontal
public import Colib.Topology.Prespectrum.RelativeHomotopyWhiskering

/-! # Relative comparison of the two original geometric unit routes

Realizing the equal normalized categorical triangles compares the two paths. The original
split geometric unit and composition tracks then give the two exact boundary paths, with
all homotopy and structure parameters independent.

Implementation provenance: Quillen `BoundedFlat/NormalizedUnitRoutes.lean:23-42,55-69,111-178`
and `BoundedFlat/OriginalUnitSquare.lean:26-63` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.IteratedS AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Topology.LoopPrespectrum
universe u v

namespace CategoryTheory.Waldhausen.IteratedS

/-- Equality transports of original exact functors preserve every transformation-track value. -/
theorem originalPrespectrumTransformationHomotopy_congr_level
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (W : Structure C) (V : Structure D) {F G F' G' : C ⥤ D}
    (hF : IsExact W.cof W.weq V.cof V.weq F)
    (hG : IsExact W.cof W.weq V.cof V.weq G)
    (hF' : IsExact W.cof W.weq V.cof V.weq F')
    (hG' : IsExact W.cof W.weq V.cof V.weq G')
    (h0F : F.obj W.zero = V.zero) (h0G : G.obj W.zero = V.zero)
    (h0F' : F'.obj W.zero = V.zero) (h0G' : G'.obj W.zero = V.zero)
    (eF : F = F') (eG : G = G') (η : F ⟶ G) (η' : F' ⟶ G')
    (hη : ∀ A, V.weq (η.app A)) (hη' : ∀ A, V.weq (η'.app A))
    (he : η ≫ eqToHom eG = eqToHom eF ≫ η') (n : ℕ) :
    (originalPrespectrumTransformationHomotopy W V hF hG h0F h0G η hη).level n =
      (originalPrespectrumTransformationHomotopy W V hF' hG' h0F' h0G' η' hη').level n := by
  subst F'
  subst G'
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at he
  subst η'
  rfl

end CategoryTheory.Waldhausen.IteratedS

namespace AlgebraicGeometry.Scheme.Modules

/-- The right unit route keeps the original composition time and unit time. -/
def boundedAboveFlatPerfectNormalizedRightUnitRoute {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Homotopy (boundedAboveFlatPerfectPullbackPrespectrumMap f)
      (boundedAboveFlatPerfectPullbackPrespectrumMap f) :=
  ((boundedAboveFlatPerfectNormalizedCompTrack (𝟙 X) f).cast
    (congrArg boundedAboveFlatPerfectPullbackPrespectrumMap (Category.id_comp f)) rfl).trans
      ((Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap f)
        (boundedAboveFlatPerfectNormalizedIdTrack X)).cast rfl (Category.comp_id _))

/-- The left unit route uses the same original target and the other geometric unit. -/
def boundedAboveFlatPerfectNormalizedLeftUnitRoute {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Homotopy (boundedAboveFlatPerfectPullbackPrespectrumMap f)
      (boundedAboveFlatPerfectPullbackPrespectrumMap f) :=
  ((boundedAboveFlatPerfectNormalizedCompTrack f (𝟙 Y)).cast
    (congrArg boundedAboveFlatPerfectPullbackPrespectrumMap (Category.comp_id f)) rfl).trans
      (((boundedAboveFlatPerfectNormalizedIdTrack Y).postcomp
        (boundedAboveFlatPerfectPullbackPrespectrumMap f)).cast rfl (Category.id_comp _))

/-- The two entire normalized unit routes compare by their actual original weak triangles. -/
def boundedAboveFlatPerfectNormalizedUnitRoutesComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (boundedAboveFlatPerfectNormalizedRightUnitRoute f).RelHomotopy
      (boundedAboveFlatPerfectNormalizedLeftUnitRoute f) := by
  let W := boundedAboveFlatPerfectWaldhausen Y.toRingedSpace
  let U := boundedAboveFlatPerfectWaldhausen X.toRingedSpace
  let hf := boundedAboveFlatPerfectNormalizedPullback_exact f
  let hx := boundedAboveFlatPerfectNormalizedPullback_exact (𝟙 X)
  let hy := boundedAboveFlatPerfectNormalizedPullback_exact (𝟙 Y)
  have J := originalPrespectrumPastingHomotopy W U hf (hf.comp hx) (hy.comp hf) hf
    (boundedAboveFlatPerfectNormalizedPullback_obj_zero f)
    ((congrArg (boundedAboveFlatPerfectNormalizedPullback (𝟙 X)).obj
      (boundedAboveFlatPerfectNormalizedPullback_obj_zero f)).trans
        (boundedAboveFlatPerfectNormalizedPullback_obj_zero (𝟙 X)))
    ((congrArg (boundedAboveFlatPerfectNormalizedPullback f).obj
      (boundedAboveFlatPerfectNormalizedPullback_obj_zero (𝟙 Y))).trans
        (boundedAboveFlatPerfectNormalizedPullback_obj_zero f))
    (boundedAboveFlatPerfectNormalizedPullback_obj_zero f)
    (boundedAboveFlatPerfectNormalizedRightUnitFirst f).hom
    (boundedAboveFlatPerfectNormalizedRightUnitSecond f).hom
    (boundedAboveFlatPerfectNormalizedLeftUnitFirst f).hom
    (boundedAboveFlatPerfectNormalizedLeftUnitSecond f).hom
    (fun _ ↦ U.weq_iso _ inferInstance) (fun _ ↦ U.weq_iso _ inferInstance)
    (fun _ ↦ U.weq_iso _ inferInstance) (fun _ ↦ U.weq_iso _ inferInstance)
    (boundedAboveFlatPerfectNormalizedUnitRoutes_equation f)
  refine J.ofLevels _ _ ?_ ?_
  · intro n
    apply Homotopy.trans_level_congr
    · rw [Homotopy.cast_level]
      unfold boundedAboveFlatPerfectNormalizedCompTrack
      rw [Homotopy.cast_level]
      apply originalPrespectrumTransformationHomotopy_congr_level
        W U _ _ _ _ _ _ _ _
        (congrArg boundedAboveFlatPerfectNormalizedPullback (Category.id_comp f)) rfl
      simp [boundedAboveFlatPerfectNormalizedRightUnitFirst]
    · have h := originalPrespectrumTransformationHomotopy_precomp_level hf hx
        (IsExact.id U.cof U.weq)
        (boundedAboveFlatPerfectNormalizedPullback_obj_zero f)
        (boundedAboveFlatPerfectNormalizedPullback_obj_zero (𝟙 X)) rfl
        (boundedAboveFlatPerfectNormalizedPullbackIdIso X).hom
        (fun _ ↦ U.weq_iso _ inferInstance) n
      refine h.symm.trans ?_
      apply originalPrespectrumTransformationHomotopy_congr_level
        W U _ _ _ _ _ _ _ _ rfl rfl
      apply NatTrans.ext
      funext A
      simp only [eqToHom_refl, Category.comp_id, Category.id_comp,
        boundedAboveFlatPerfectNormalizedRightUnitSecond, Iso.trans_hom, isoWhiskerLeft_hom,
        NatTrans.comp_app, rightUnitor_hom_app]
      exact (Category.comp_id _).symm
  · intro n
    apply Homotopy.trans_level_congr
    · rw [Homotopy.cast_level]
      unfold boundedAboveFlatPerfectNormalizedCompTrack
      rw [Homotopy.cast_level]
      apply originalPrespectrumTransformationHomotopy_congr_level
        W U _ _ _ _ _ _ _ _
        (congrArg boundedAboveFlatPerfectNormalizedPullback (Category.comp_id f)) rfl
      simp [boundedAboveFlatPerfectNormalizedLeftUnitFirst]
    · have h := originalPrespectrumTransformationHomotopy_postcomp_level hy
        (IsExact.id W.cof W.weq) hf
        (boundedAboveFlatPerfectNormalizedPullback_obj_zero (𝟙 Y)) rfl
        (boundedAboveFlatPerfectNormalizedPullback_obj_zero f)
        (boundedAboveFlatPerfectNormalizedPullbackIdIso Y).hom
        (fun _ ↦ W.weq_iso _ inferInstance) n
      refine h.symm.trans ?_
      apply originalPrespectrumTransformationHomotopy_congr_level
        W U _ _ _ _ _ _ _ _ rfl rfl
      apply NatTrans.ext
      funext A
      simp only [eqToHom_refl, Category.comp_id, Category.id_comp,
        boundedAboveFlatPerfectNormalizedLeftUnitSecond, Iso.trans_hom, isoWhiskerRight_hom,
        NatTrans.comp_app, leftUnitor_hom_app]
      exact (Category.comp_id _).symm

/-- The right geometric unit route retains both the binary and identity normalizations. -/
def boundedAboveFlatPerfectOriginalRightUnitRoute {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Homotopy (boundedAboveFlatPerfectPullbackPrespectrumMap f)
      (boundedAboveFlatPerfectPullbackPrespectrumMap f) :=
  ((boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy (𝟙 X) f).cast
    (congrArg boundedAboveFlatPerfectPullbackPrespectrumMap (Category.id_comp f)) rfl).trans
      ((Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap f)
        (boundedAboveFlatPerfectPullbackPrespectrumIdHomotopy X)).cast rfl (Category.comp_id _))

/-- The left geometric unit route retains both original normalization pieces. -/
def boundedAboveFlatPerfectOriginalLeftUnitRoute {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Homotopy (boundedAboveFlatPerfectPullbackPrespectrumMap f)
      (boundedAboveFlatPerfectPullbackPrespectrumMap f) :=
  ((boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy f (𝟙 Y)).cast
    (congrArg boundedAboveFlatPerfectPullbackPrespectrumMap (Category.comp_id f)) rfl).trans
      (((boundedAboveFlatPerfectPullbackPrespectrumIdHomotopy Y).postcomp
        (boundedAboveFlatPerfectPullbackPrespectrumMap f)).cast rfl (Category.id_comp _))

/-- The right route's two full composition triangles identify its original split tracks. -/
def boundedAboveFlatPerfectNormalizedRightUnitRouteComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (boundedAboveFlatPerfectNormalizedRightUnitRoute f).RelHomotopy
      (boundedAboveFlatPerfectOriginalRightUnitRoute f) :=
  ((boundedAboveFlatPerfectNormalizedCompTrackComparison (𝟙 X) f).cast
    (congrArg boundedAboveFlatPerfectPullbackPrespectrumMap (Category.id_comp f)) rfl).hcomp
      ((Homotopy.RelHomotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap f)
        (boundedAboveFlatPerfectNormalizedIdTrackComparison X)).cast rfl (Category.comp_id _))

/-- The left route's two full composition triangles identify its original split tracks. -/
def boundedAboveFlatPerfectNormalizedLeftUnitRouteComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (boundedAboveFlatPerfectNormalizedLeftUnitRoute f).RelHomotopy
      (boundedAboveFlatPerfectOriginalLeftUnitRoute f) :=
  ((boundedAboveFlatPerfectNormalizedCompTrackComparison f (𝟙 Y)).cast
    (congrArg boundedAboveFlatPerfectPullbackPrespectrumMap (Category.comp_id f)) rfl).hcomp
      (((boundedAboveFlatPerfectNormalizedIdTrackComparison Y).postcomp
        (boundedAboveFlatPerfectPullbackPrespectrumMap f)).cast rfl (Category.id_comp _))

/-- Both whole ORIGINAL unit routes agree through their actual normalized unit triangles. -/
def boundedAboveFlatPerfectOriginalUnitRoutesComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (boundedAboveFlatPerfectOriginalRightUnitRoute f).RelHomotopy
      (boundedAboveFlatPerfectOriginalLeftUnitRoute f) :=
  (boundedAboveFlatPerfectNormalizedRightUnitRouteComparison f).symm.trans
    ((boundedAboveFlatPerfectNormalizedUnitRoutesComparison f).trans
      (boundedAboveFlatPerfectNormalizedLeftUnitRouteComparison f))

end AlgebraicGeometry.Scheme.Modules
