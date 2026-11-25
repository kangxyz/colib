/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumComposition
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectUnitHomotopy
public import Colib.KTheory.Waldhausen.Iterated.ExactPastingHomotopy
public import Colib.KTheory.Waldhausen.Iterated.NormalizationTrackPasting
public import Colib.Topology.Prespectrum.RelativeHomotopyHorizontal
public import Colib.Topology.Prespectrum.RelativeHomotopyReparam

/-!
# Scalar unit tracks and geometric pullback composition

The two relative homotopies intertwine the original unit track with both the
geometric and chosen-zero normalization portions of the prespectrum composition
track. The bounded-above flat complexes permit arbitrary scheme pullbacks.

Adapted from Quillen `BoundedFlat/UnitTrack.lean:27-113` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open Topology.LoopPrespectrum AlgebraicGeometry.RingedSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The geometric comparison intertwines the source unit with its actual scalar pullback. -/
theorem boundedAboveFlatPerfectPullbackUnitIso_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (r : (Γ(Y, ⊤))ˣ) :
    (boundedAboveFlatPerfectPullbackCompIso f g).hom ≫
      Functor.whiskerRight (boundedAboveFlatPerfectPullbackUnitIso g r).hom
        (boundedAboveFlatPerfectPullback f) =
    (boundedAboveFlatPerfectPullbackUnitIso (f ≫ g)
      (Units.map f.appTop.hom.toMonoidHom r)).hom ≫
      (boundedAboveFlatPerfectPullbackCompIso f g).hom := by
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, boundedAboveFlatPerfectPullbackUnitIso, Iso.trans_hom,
    Iso.symm_hom, Functor.rightUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  simp only [Category.comp_id]
  rw [boundedAboveFlatPerfectPullback_map_globalUnit]
  exact (boundedAboveFlatPerfectGlobalUnitIso X
    (Units.map f.appTop.hom.toMonoidHom r)).hom.naturality _

/-- Postwhiskering an actual unit commutes relatively with the original composition track. -/
def boundedAboveFlatPerfectUnitTrackPostcomp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (r : (Γ(Y, ⊤))ˣ) :
    ((boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy f g).trans
      ((boundedAboveFlatPerfectUnitHomotopy g r).postcomp
        (boundedAboveFlatPerfectPullbackPrespectrumMap f))).RelHomotopy
    ((boundedAboveFlatPerfectUnitHomotopy (f ≫ g) (Units.map f.appTop.hom.toMonoidHom r)).trans
      (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy f g)) := by
  let V := boundedAboveFlatPerfectWaldhausen Z.toRingedSpace
  let U := boundedAboveFlatPerfectWaldhausen X.toRingedSpace
  let hA := boundedAboveFlatPerfectPullback_isExact (f ≫ g)
  let hB := (boundedAboveFlatPerfectPullback_isExact g).comp
    (boundedAboveFlatPerfectPullback_isExact f)
  let e := boundedAboveFlatPerfectPullbackCompIso f g
  let a := boundedAboveFlatPerfectPullbackUnitIso (f ≫ g) (Units.map f.appTop.hom.toMonoidHom r)
  let b := Functor.isoWhiskerRight (boundedAboveFlatPerfectPullbackUnitIso g r)
    (boundedAboveFlatPerfectPullback f)
  let G := exactOriginalPrespectrumIsoHomotopy V U hA hB e
  let B := exactOriginalPrespectrumIsoHomotopy V U hB hB b
  let A := boundedAboveFlatPerfectUnitHomotopy (f ≫ g) (Units.map f.appTop.hom.toMonoidHom r)
  let M := boundedAboveFlatPerfectWaldhausen Y.toRingedSpace
  let N := exactOriginalPrespectrumMapCompHomotopy V M U
    (boundedAboveFlatPerfectPullback_isExact g) (boundedAboveFlatPerfectPullback_isExact f)
  let D := (boundedAboveFlatPerfectUnitHomotopy g r).postcomp
    (boundedAboveFlatPerfectPullbackPrespectrumMap f)
  have JG : (G.trans B).RelHomotopy (A.trans G) :=
    exactOriginalPrespectrumPastingHomotopy V U hA hB hA hB
      e.hom b.hom a.hom e.hom (fun _ ↦ U.weq_iso _ inferInstance)
      (fun _ ↦ U.weq_iso _ inferInstance) (fun _ ↦ U.weq_iso _ inferInstance)
      (fun _ ↦ U.weq_iso _ inferInstance) (boundedAboveFlatPerfectPullbackUnitIso_comp f g r)
  have JN : (B.trans N).RelHomotopy (N.trans D) :=
    exactNormalizationLeftTrackPasting (boundedAboveFlatPerfectPullback_isExact g)
      (boundedAboveFlatPerfectPullback_isExact g) (boundedAboveFlatPerfectPullback_isExact f)
      (boundedAboveFlatPerfectPullbackUnitIso g r).hom
      (fun _ ↦ M.weq_iso _ inferInstance)
  exact (Homotopy.RelHomotopy.transAssoc G N D).trans
    (((Homotopy.RelHomotopy.refl G).hcomp JN.symm).trans
      ((Homotopy.RelHomotopy.transAssoc G B N).symm.trans
        ((JG.hcomp (Homotopy.RelHomotopy.refl N)).trans
          (Homotopy.RelHomotopy.transAssoc A G N))))

/-- The target scalar intertwines the genuine geometric pullback composition comparison. -/
lemma boundedAboveFlatPerfectPullbackUnitIso_comp_target {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (r : (Γ(X, ⊤))ˣ) :
    (boundedAboveFlatPerfectPullbackCompIso f g).hom ≫
      Functor.whiskerLeft (boundedAboveFlatPerfectPullback g)
        (boundedAboveFlatPerfectPullbackUnitIso f r).hom =
    (boundedAboveFlatPerfectPullbackUnitIso (f ≫ g) r).hom ≫
      (boundedAboveFlatPerfectPullbackCompIso f g).hom := by
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, boundedAboveFlatPerfectPullbackUnitIso, Iso.trans_hom,
    Iso.symm_hom, Functor.rightUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.id_comp]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  simp only [Category.comp_id]
  exact (boundedAboveFlatPerfectGlobalUnitIso X r).hom.naturality _

/-- Prewhiskering an actual unit commutes relatively with the original composition track. -/
def boundedAboveFlatPerfectUnitTrackPrecomp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (r : (Γ(X, ⊤))ˣ) :
    ((boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy f g).trans
      (Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap g)
        (boundedAboveFlatPerfectUnitHomotopy f r))).RelHomotopy
    ((boundedAboveFlatPerfectUnitHomotopy (f ≫ g) r).trans
      (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy f g)) := by
  let V := boundedAboveFlatPerfectWaldhausen Z.toRingedSpace
  let U := boundedAboveFlatPerfectWaldhausen X.toRingedSpace
  let hA := boundedAboveFlatPerfectPullback_isExact (f ≫ g)
  let hB := (boundedAboveFlatPerfectPullback_isExact g).comp
    (boundedAboveFlatPerfectPullback_isExact f)
  let e := boundedAboveFlatPerfectPullbackCompIso f g
  let a := boundedAboveFlatPerfectPullbackUnitIso (f ≫ g) r
  let b := Functor.isoWhiskerLeft (boundedAboveFlatPerfectPullback g)
    (boundedAboveFlatPerfectPullbackUnitIso f r)
  let G := exactOriginalPrespectrumIsoHomotopy V U hA hB e
  let B := exactOriginalPrespectrumIsoHomotopy V U hB hB b
  let A := boundedAboveFlatPerfectUnitHomotopy (f ≫ g) r
  let M := boundedAboveFlatPerfectWaldhausen Y.toRingedSpace
  let N := exactOriginalPrespectrumMapCompHomotopy V M U
    (boundedAboveFlatPerfectPullback_isExact g) (boundedAboveFlatPerfectPullback_isExact f)
  let D := Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap g)
    (boundedAboveFlatPerfectUnitHomotopy f r)
  have JG : (G.trans B).RelHomotopy (A.trans G) :=
    exactOriginalPrespectrumPastingHomotopy V U hA hB hA hB
      e.hom b.hom a.hom e.hom (fun _ ↦ U.weq_iso _ inferInstance)
      (fun _ ↦ U.weq_iso _ inferInstance) (fun _ ↦ U.weq_iso _ inferInstance)
      (fun _ ↦ U.weq_iso _ inferInstance)
      (boundedAboveFlatPerfectPullbackUnitIso_comp_target f g r)
  have JN : (B.trans N).RelHomotopy (N.trans D) :=
    exactNormalizationRightTrackPasting (boundedAboveFlatPerfectPullback_isExact g)
      (boundedAboveFlatPerfectPullback_isExact f) (boundedAboveFlatPerfectPullback_isExact f)
      (boundedAboveFlatPerfectPullbackUnitIso f r).hom
      (fun _ ↦ U.weq_iso _ inferInstance)
  exact (Homotopy.RelHomotopy.transAssoc G N D).trans
    (((Homotopy.RelHomotopy.refl G).hcomp JN.symm).trans
      ((Homotopy.RelHomotopy.transAssoc G B N).symm.trans
        ((JG.hcomp (Homotopy.RelHomotopy.refl N)).trans
          (Homotopy.RelHomotopy.transAssoc A G N))))

end AlgebraicGeometry.Scheme.Modules
