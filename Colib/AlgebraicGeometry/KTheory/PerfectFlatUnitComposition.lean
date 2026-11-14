/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectFlatUnitHomotopy
public import Colib.AlgebraicGeometry.Modules.PerfectFlatPullbackComposition
public import Colib.KTheory.Waldhausen.Iterated.ExactPastingHomotopy
public import Colib.KTheory.Waldhausen.Iterated.ExactCoherence
public import Colib.KTheory.Waldhausen.Iterated.NormalizationTrackPasting
public import Colib.KTheory.Waldhausen.Iterated.SelfTrackKOperationNaturality
public import Colib.KTheory.Waldhausen.Iterated.SelfTrackKOperationIntertwining
public import Colib.Topology.Prespectrum.RelativeHomotopyReparam
public import StacksFrontier.AlgebraicGeometry.Modules.GlobalSmulPullback

/-! # Naturality of the native flat Laurent unit operation -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open Topology.LoopPrespectrum

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
namespace AlgebraicGeometry.Scheme.Modules

local notation "W" Y =>
  RingedSpace.perfectComplexesWaldhausen (LocallyRingedSpace.toRingedSpace
    (Scheme.toLocallyRingedSpace Y))

/-- Flat geometric pullback preserves the actual native scalar automorphism. -/
theorem perfectFlatPullback_map_globalUnit {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (q : (Γ(Y, ⊤))ˣ) (K : ObjectProperty.FullSubcategory
      (RingedSpace.IsPerfectComplex (X := Y.toRingedSpace))) :
    (perfectFlatPullback f).map ((perfectGlobalUnitIso Y q).hom.app K) =
      (perfectGlobalUnitIso X (Units.map f.appTop.hom.toMonoidHom q)).hom.app
        ((perfectFlatPullback f).obj K) := by
  apply ObjectProperty.hom_ext
  ext j : 1
  exact Stacks.RegularSequence.pullback_map_globalSmulCenter f (↑q) (K.obj.X j)

/-- The geometric track for composition compares native pullback with the composite map. -/
def perfectFlatPrespectrumCompHomotopy {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [Flat g] :
    Topology.LoopPrespectrum.Homotopy (perfectFlatPrespectrumMap (f ≫ g))
      (perfectFlatPrespectrumMap g ≫ perfectFlatPrespectrumMap f) :=
  (exactOriginalPrespectrumIsoHomotopy (W Z) (W X)
    (perfectFlatPullback_waldhausenExact (f ≫ g))
    ((perfectFlatPullback_waldhausenExact g).comp (perfectFlatPullback_waldhausenExact f))
    (perfectFlatPullbackComp f g).symm).trans
    (exactOriginalPrespectrumMapCompHomotopy (W Z) (W Y) (W X)
      (perfectFlatPullback_waldhausenExact g) (perfectFlatPullback_waldhausenExact f))

/-- The original geometric composition iso intertwines the actual pulled-back source unit. -/
theorem perfectFlatPullbackUnitIso_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [Flat g] (r : (Γ(Y, ⊤))ˣ) :
    ((perfectFlatPullbackComp f g).symm).hom ≫
      Functor.whiskerRight (perfectFlatPullbackUnitIso g r).hom (perfectFlatPullback f) =
    (perfectFlatPullbackUnitIso (f ≫ g) (Units.map f.appTop.hom.toMonoidHom r)).hom ≫
      ((perfectFlatPullbackComp f g).symm).hom := by
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, perfectFlatPullbackUnitIso, Iso.trans_hom,
    Iso.symm_hom, Functor.rightUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  simp only [Category.comp_id]
  rw [perfectFlatPullback_map_globalUnit]
  exact (perfectGlobalUnitIso X (Units.map f.appTop.hom.toMonoidHom r)).hom.naturality _

/-- Postwhiskering an actual unit commutes relatively with the original composition track. -/
def perfectFlatUnitTrackPostcomp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [Flat g] (r : (Γ(Y, ⊤))ˣ) :
    ((perfectFlatPrespectrumCompHomotopy f g).trans
      ((perfectFlatUnitHomotopy g r).postcomp
        (perfectFlatPrespectrumMap f))).RelHomotopy
    ((perfectFlatUnitHomotopy (f ≫ g) (Units.map f.appTop.hom.toMonoidHom r)).trans
      (perfectFlatPrespectrumCompHomotopy f g)) := by
  let V := W Z
  let U := W X
  let hA := perfectFlatPullback_waldhausenExact (f ≫ g)
  let hB := (perfectFlatPullback_waldhausenExact g).comp (perfectFlatPullback_waldhausenExact f)
  let e := (perfectFlatPullbackComp f g).symm
  let a := perfectFlatPullbackUnitIso (f ≫ g) (Units.map f.appTop.hom.toMonoidHom r)
  let b := Functor.isoWhiskerRight (perfectFlatPullbackUnitIso g r)
    (perfectFlatPullback f)
  let G := exactOriginalPrespectrumIsoHomotopy V U hA hB e
  let B := exactOriginalPrespectrumIsoHomotopy V U hB hB b
  let A := perfectFlatUnitHomotopy (f ≫ g) (Units.map f.appTop.hom.toMonoidHom r)
  let N := exactOriginalPrespectrumMapCompHomotopy V (W Y) U
    (perfectFlatPullback_waldhausenExact g) (perfectFlatPullback_waldhausenExact f)
  let D := (perfectFlatUnitHomotopy g r).postcomp (perfectFlatPrespectrumMap f)
  have JG : (G.trans B).RelHomotopy (A.trans G) :=
    exactOriginalPrespectrumPastingHomotopy V U hA hB hA hB
      e.hom b.hom a.hom e.hom (fun _ ↦ U.weq_iso _ inferInstance)
      (fun _ ↦ U.weq_iso _ inferInstance) (fun _ ↦ U.weq_iso _ inferInstance)
      (fun _ ↦ U.weq_iso _ inferInstance) (perfectFlatPullbackUnitIso_comp f g r)
  have JN : (B.trans N).RelHomotopy (N.trans D) :=
    exactNormalizationLeftTrackPasting (perfectFlatPullback_waldhausenExact g)
      (perfectFlatPullback_waldhausenExact g) (perfectFlatPullback_waldhausenExact f)
      (perfectFlatPullbackUnitIso g r).hom
      (fun _ ↦ (W Y).weq_iso _ inferInstance)
  exact (Homotopy.RelHomotopy.transAssoc G N D).trans
    (((Homotopy.RelHomotopy.refl G).hcomp JN.symm).trans
      ((Homotopy.RelHomotopy.transAssoc G B N).symm.trans
        ((JG.hcomp (Homotopy.RelHomotopy.refl N)).trans
          (Homotopy.RelHomotopy.transAssoc A G N))))

/-- The target scalar intertwines the genuine geometric pullback composition comparison. -/
lemma perfectFlatPullbackUnitIso_comp_target {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [Flat g] (r : (Γ(X, ⊤))ˣ) :
    ((perfectFlatPullbackComp f g).symm).hom ≫
      Functor.whiskerLeft (perfectFlatPullback g)
        (perfectFlatPullbackUnitIso f r).hom =
    (perfectFlatPullbackUnitIso (f ≫ g) r).hom ≫
      ((perfectFlatPullbackComp f g).symm).hom := by
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, perfectFlatPullbackUnitIso, Iso.trans_hom,
    Iso.symm_hom, Functor.rightUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.id_comp]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  simp only [Category.comp_id]
  exact (perfectGlobalUnitIso X r).hom.naturality _

/-- Prewhiskering an actual unit commutes relatively with the original composition track. -/
def perfectFlatUnitTrackPrecomp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [Flat g] (r : (Γ(X, ⊤))ˣ) :
    ((perfectFlatPrespectrumCompHomotopy f g).trans
      (Homotopy.precomp (perfectFlatPrespectrumMap g)
        (perfectFlatUnitHomotopy f r))).RelHomotopy
    ((perfectFlatUnitHomotopy (f ≫ g) r).trans
      (perfectFlatPrespectrumCompHomotopy f g)) := by
  let V := W Z
  let U := W X
  let hA := perfectFlatPullback_waldhausenExact (f ≫ g)
  let hB := (perfectFlatPullback_waldhausenExact g).comp (perfectFlatPullback_waldhausenExact f)
  let e := (perfectFlatPullbackComp f g).symm
  let a := perfectFlatPullbackUnitIso (f ≫ g) r
  let b := Functor.isoWhiskerLeft (perfectFlatPullback g)
    (perfectFlatPullbackUnitIso f r)
  let G := exactOriginalPrespectrumIsoHomotopy V U hA hB e
  let B := exactOriginalPrespectrumIsoHomotopy V U hB hB b
  let A := perfectFlatUnitHomotopy (f ≫ g) r
  let N := exactOriginalPrespectrumMapCompHomotopy V (W Y) U
    (perfectFlatPullback_waldhausenExact g) (perfectFlatPullback_waldhausenExact f)
  let D := Homotopy.precomp (perfectFlatPrespectrumMap g)
    (perfectFlatUnitHomotopy f r)
  have JG : (G.trans B).RelHomotopy (A.trans G) :=
    exactOriginalPrespectrumPastingHomotopy V U hA hB hA hB
      e.hom b.hom a.hom e.hom (fun _ ↦ U.weq_iso _ inferInstance)
      (fun _ ↦ U.weq_iso _ inferInstance) (fun _ ↦ U.weq_iso _ inferInstance)
      (fun _ ↦ U.weq_iso _ inferInstance) (perfectFlatPullbackUnitIso_comp_target f g r)
  have JN : (B.trans N).RelHomotopy (N.trans D) :=
    exactNormalizationRightTrackPasting (perfectFlatPullback_waldhausenExact g)
      (perfectFlatPullback_waldhausenExact f) (perfectFlatPullback_waldhausenExact f)
      (perfectFlatPullbackUnitIso f r).hom
      (fun _ ↦ U.weq_iso _ inferInstance)
  exact (Homotopy.RelHomotopy.transAssoc G N D).trans
    (((Homotopy.RelHomotopy.refl G).hcomp JN.symm).trans
      ((Homotopy.RelHomotopy.transAssoc G B N).symm.trans
        ((JG.hcomp (Homotopy.RelHomotopy.refl N)).trans
          (Homotopy.RelHomotopy.transAssoc A G N))))


/-- Flat target pullback preserves the complete original unit operation in every degree. -/
theorem perfectFlatUnitHomotopy_originalKOperation_postcomp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [Flat g]
    (r : (Γ(Y, ⊤))ˣ) (n : ℕ) :
    (KMap (perfectFlatPullback_waldhausenExact f) (n + 1)).comp
      (originalKSelfTrackOperation (W Z) (W Y)
        (perfectFlatUnitHomotopy g r) n) =
    originalKSelfTrackOperation (W Z) (W X)
      (perfectFlatUnitHomotopy (f ≫ g) (Units.map f.appTop.hom.toMonoidHom r)) n := by
  rw [← originalKSelfTrackOperation_postcomp]
  exact (originalKSelfTrackOperation_intertwine (W Z) (W X)
    (perfectFlatUnitHomotopy (f ≫ g) (Units.map f.appTop.hom.toMonoidHom r))
    ((perfectFlatUnitHomotopy g r).postcomp (perfectFlatPrespectrumMap f))
    (perfectFlatPrespectrumCompHomotopy f g) (perfectFlatUnitTrackPostcomp f g r).symm n).symm

/-- Flat source pullback preserves the complete original unit operation in every degree. -/
theorem perfectFlatUnitHomotopy_originalKOperation_precomp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [Flat g]
    (q : (Γ(X, ⊤))ˣ) (n : ℕ) :
    (originalKSelfTrackOperation (W Y) (W X)
      (perfectFlatUnitHomotopy f q) n).comp (KMap (perfectFlatPullback_waldhausenExact g) n) =
    originalKSelfTrackOperation (W Z) (W X)
      (perfectFlatUnitHomotopy (f ≫ g) q) n := by
  rw [← originalKSelfTrackOperation_precomp]
  exact (originalKSelfTrackOperation_intertwine (W Z) (W X)
    (perfectFlatUnitHomotopy (f ≫ g) q)
    (Homotopy.precomp (perfectFlatPrespectrumMap g) (perfectFlatUnitHomotopy f q))
    (perfectFlatPrespectrumCompHomotopy f g) (perfectFlatUnitTrackPrecomp f g q).symm n).symm

/-- Equal scheme morphisms induce the same original Laurent unit operation. -/
theorem perfectFlatUnitHomotopy_originalKOperation_congr {X Y : Scheme.{u}}
    {f g : X ⟶ Y} [Flat f] [Flat g] (h : f = g) (q : (Γ(X, ⊤))ˣ) (n : ℕ) :
    originalKSelfTrackOperation (W Y) (W X) (perfectFlatUnitHomotopy f q) n =
      originalKSelfTrackOperation (W Y) (W X) (perfectFlatUnitHomotopy g q) n := by
  subst g
  rfl

end AlgebraicGeometry.Scheme.Modules
