/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSupportedRow
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinarySupportedBassSeed

/-! # Original global Laurent action restricted to actual support -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open KTheory.Bass CategoryTheory.Functor.IdentityAutomorphism
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex

private theorem preservesRestricted {C D : Type*} [Category C] [Category D]
    (P : ObjectProperty C) (Q : ObjectProperty D) (F : C ⥤ D)
    (hF : ∀ x : P.FullSubcategory, Q (F.obj x.obj))
    (α : 𝟭 C ≅ 𝟭 C) (β : 𝟭 D ≅ 𝟭 D) (h : Preserves F α β) :
    Preserves (Q.lift (P.ι ⋙ F) hF) (lift P.ι α) (lift Q.ι β) := by
  intro x
  apply ObjectProperty.hom_ext
  change F.map (((lift P.ι α).hom.app x).hom) =
    ((lift Q.ι β).hom.app ((Q.lift (P.ι ⋙ F) hF).obj x)).hom
  rw [show ((lift P.ι α).hom.app x).hom = α.hom.app x.obj from map_lift_hom P.ι α x,
    show ((lift Q.ι β).hom.app ((Q.lift (P.ι ⋙ F) hF).obj x)).hom =
      β.hom.app (F.obj x.obj) from map_lift_hom Q.ι β _]
  exact h x.obj

variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

/-- The actual forward global Laurent unit on the original supported full subcategory. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedAction.lean:42"
  "adaptation" "Actual supported global unit and whole forgetful seed square"]
def supportedLaurentUnit (a : Under R) :
    𝟭 (rowSupported f ((laurentUnderFunctor R).obj a)).FullSubcategory ≅
      𝟭 (rowSupported f ((laurentUnderFunctor R).obj a)).FullSubcategory :=
  lift (rowSupported f ((laurentUnderFunctor R).obj a)).ι (globalLaurentUnit Q a)

/-- Original supported reindexing preserves this same forward unit. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedAction.lean:48"
  "adaptation" "Actual supported global unit and whole forgetful seed square"]
theorem supportedLaurentUnit_naturality {a b : Under R} (g : a ⟶ b) :
    Preserves ((supportedRow f).map ((laurentUnderFunctor R).map g)).hom.toFunctor
      (supportedLaurentUnit f a) (supportedLaurentUnit f b) :=
  preservesRestricted (rowSupported f ((laurentUnderFunctor R).obj a))
    (rowSupported f ((laurentUnderFunctor R).obj b))
    ((globalRow Q).map ((laurentUnderFunctor R).map g)).hom.toFunctor
    (fun x => rowMap_supported f ((laurentUnderFunctor R).map g) x.obj x.property)
    _ _ (globalLaurentUnit_naturality Q g)

/-- The supported global seed action retains the original Laurent unit. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedAction.lean:58"
  "adaptation" "Actual supported global unit and whole forgetful seed square"]
def supportedLaurentAction : LaurentSeed.ModelAction (supportedRow f) where
  unit := supportedLaurentUnit f
  naturality := supportedLaurentUnit_naturality f


/-- Actual coefficient restriction preserves the entire original supported unit. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedAction.lean:63"
  "adaptation" "Original supported restriction whole unit, track and seed square"]
theorem supportedRowRestriction_unit (a : Under R) :
    Preserves ((supportedRowRestriction f).app ((laurentUnderFunctor R).obj a)).hom.toFunctor
      ((supportedLaurentAction f).unit a)
      ((boundedAboveFlatCoefficientSupportedLaurentAction f).unit a) :=
  preservesRestricted (rowSupported f ((laurentUnderFunctor R).obj a))
    (boundedAboveFlatCoefficientSectionSupported (schemeMap f ((laurentUnderFunctor R).obj a)))
    ((rowRestriction Q).app ((laurentUnderFunctor R).obj a)).hom.toFunctor _ _ _
    (rowRestriction_unit Q a)

/-- Actual restriction retains every time of the supported Laurent track. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedAction.lean:73"
  "adaptation" "Original supported restriction whole unit, track and seed square"]
theorem supportedRowRestriction_track (a : Under R) (n : ℕ) (t : unitInterval)
    (x : (prespectrum ((supportedRow f).obj a)).space n) :
    (prespectrumMap ((supportedRowRestriction f).app ((laurentUnderFunctor R).obj a))).map n
      (((supportedLaurentAction f).track.homotopy a).level n (t, x)) =
    ((boundedAboveFlatCoefficientSupportedLaurentAction f).track.homotopy a).level n
      (t, (prespectrumMap ((supportedRowRestriction f).app a)).map n x) :=
  LaurentSeed.ModelAction.track_square _ _ _ (supportedRowRestriction_unit f) a n t x

/-- The supported original seed commutes strictly with coefficient restriction. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedAction.lean:82"
  "adaptation" "Original supported restriction whole unit, track and seed square"]
theorem supportedRowRestriction_seed :
    (supportedLaurentAction f).track.seed ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (Functor.whiskerRight (supportedRowRestriction f) prespectrumFunctor) =
    Functor.whiskerRight (supportedRowRestriction f) prespectrumFunctor ≫
      (boundedAboveFlatCoefficientSupportedLaurentAction f).track.seed :=
  LaurentSeed.Track.seed_square _ _ _ (supportedRowRestriction_track f)

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
