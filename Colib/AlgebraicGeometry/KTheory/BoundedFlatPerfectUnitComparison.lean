/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumPullback
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectUnitHomotopy
public import Colib.KTheory.Waldhausen.Iterated.NormalizationTrackPasting
public import Colib.Topology.Prespectrum.SelfTrackIntertwining
public import Colib.Topology.Prespectrum.SelfTrackStableNaturality

/-! # Flat scalar operations and the original inclusion into perfect complexes -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open AlgebraicGeometry AlgebraicGeometry.RingedSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The literal inclusion of bounded-above flat complexes retains the actual global scalar. -/
theorem boundedAboveFlatPerfectPullbackUnitIso_inclusion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] (r : (Γ(X, ⊤))ˣ) :
    whiskerRight (boundedAboveFlatPerfectPullbackUnitIso f r).hom
        (boundedAboveFlatPerfectInclusion X.toRingedSpace) =
      whiskerLeft (boundedAboveFlatPerfectInclusion Y.toRingedSpace)
        (perfectFlatPullbackUnitIso f r).hom := by
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  simp only [boundedAboveFlatPerfectPullbackUnitIso, perfectFlatPullbackUnitIso,
    Iso.trans_hom, Iso.symm_hom, Functor.rightUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.comp_app, Category.id_comp]
  exact boundedAboveFlatPerfectGlobalUnitIso_hom_original X r _

/-- The original stable operation commutes with the original perfect inclusion. -/
theorem boundedAboveFlatPerfectUnitHomotopy_stableOperation_inclusion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] (r : (Γ(X, ⊤))ˣ) (d : ℤ) :
    (boundedAboveFlatPerfectUnitHomotopy f r).stableOperation d ≫
      (stableHomotopyFunctor (d + 1)).map
        (boundedAboveFlatPerfectToPerfectPrespectrumMap X.toRingedSpace) =
    (stableHomotopyFunctor d).map
      (boundedAboveFlatPerfectToPerfectPrespectrumMap Y.toRingedSpace) ≫
        (perfectFlatUnitHomotopy f r).stableOperation d := by
  let hF := boundedAboveFlatPerfectPullback_isExact f
  let hJ := boundedAboveFlatPerfectInclusion_isExact X.toRingedSpace
  let hI := boundedAboveFlatPerfectInclusion_isExact Y.toRingedSpace
  let hG := perfectFlatPullback_waldhausenExact f
  let η := (boundedAboveFlatPerfectPullbackUnitIso f r).hom
  let θ := (perfectFlatPullbackUnitIso f r).hom
  have hη : ∀ K, (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq (η.app K) :=
    fun _ => (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq_iso _ inferInstance
  have hθ : ∀ K, (perfectComplexesWaldhausen X.toRingedSpace).weq (θ.app K) :=
    fun _ => (perfectComplexesWaldhausen X.toRingedSpace).weq_iso _ inferInstance
  have hl := exactNormalizationLeftTrackPasting hF hF hJ η hη
  have hr := exactNormalizationRightTrackPasting hI hG hG θ hθ
  have el := Homotopy.stableOperation_intertwine _ _ _ hl d
  have er := Homotopy.stableOperation_intertwine _ _ _ hr d
  rw [Homotopy.stableOperation_postcomp] at el
  rw [Homotopy.stableOperation_precomp] at er
  have he : whiskerRight η (boundedAboveFlatPerfectInclusion X.toRingedSpace) =
      whiskerLeft (boundedAboveFlatPerfectInclusion Y.toRingedSpace) θ :=
    boundedAboveFlatPerfectPullbackUnitIso_inclusion f r
  have ee :
      (exactOriginalPrespectrumHomotopy _ _ (hF.comp hJ) (hF.comp hJ)
        (whiskerRight η (boundedAboveFlatPerfectInclusion X.toRingedSpace))
          (fun K => hJ.weak _ (hη K))).stableOperation d =
      (exactOriginalPrespectrumHomotopy _ _ (hI.comp hG) (hI.comp hG)
        (whiskerLeft (boundedAboveFlatPerfectInclusion Y.toRingedSpace) θ)
          (fun K => hθ ((boundedAboveFlatPerfectInclusion Y.toRingedSpace).obj K))
            ).stableOperation d := by
    simp only [he]
  exact el.symm.trans (ee.trans er)

end AlgebraicGeometry.Scheme.Modules
