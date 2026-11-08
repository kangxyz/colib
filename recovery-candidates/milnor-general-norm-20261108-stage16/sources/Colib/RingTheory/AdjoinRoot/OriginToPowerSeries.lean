/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Polynomial.OriginLocalMap
public import Colib.RingTheory.AdjoinRoot.PowerSeriesResidue
public import StacksFrontier.RingTheory.DiscreteValuationRing.MonicResidueIrreducible
public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.ConstantRetraction

/-!
# The original root-field origin maps to the actual constant root DVR

The actual localization of (AdjoinRoot p)[X] at (X) maps by polynomial evaluation
into AdjoinRoot (p.map PowerSeries.C). The coordinate goes to the original image
of PowerSeries.X, a uniformizer, and the existing native residue-field map becomes
the identity of the old root field through the two established residue equivalences.
No local ring, residue field, norm or completion carrier is replaced.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing Stacks.Chow

namespace AdjoinRoot

variable {k : Type*} [Field k] (p : k[X]) [Fact p.Monic] [Fact (Irreducible p)]

local instance : IsLocalRing (AdjoinRoot (p.map (PowerSeries.C : k →+* PowerSeries k))) :=
  isLocalRing_of_irreducible_map_residue ((Fact.out : p.Monic).map _)
    ((Fact.out : p.Monic).irreducible_map_powerSeries_C_residue Fact.out)

local instance : IsDomain (AdjoinRoot (p.map (PowerSeries.C : k →+* PowerSeries k))) :=
  isDomain_of_irreducible_map_residue ((Fact.out : p.Monic).map _)
    ((Fact.out : p.Monic).irreducible_map_powerSeries_C_residue Fact.out)

local instance : IsLocalHom
    (algebraMap (PowerSeries k) (AdjoinRoot (p.map (PowerSeries.C : k →+* PowerSeries k)))) := by
  rw [AdjoinRoot.algebraMap_eq]
  exact isLocalHom_of_monic ((Fact.out : p.Monic).map _)

/-- The original power-series parameter lies in the actual root algebra's maximal ideal. -/
theorem powerSeriesRoot_X_mem_maximalIdeal :
    of (p.map (PowerSeries.C : k →+* PowerSeries k)) PowerSeries.X ∈
      maximalIdeal (AdjoinRoot (p.map (PowerSeries.C : k →+* PowerSeries k))) :=
  map_nonunit (algebraMap (PowerSeries k) _) PowerSeries.X PowerSeries.X_irreducible.not_isUnit

/-- Evaluation gives the actual map from the original root-field origin local ring. -/
def originToPowerSeries :
    localRingAtOrigin (AdjoinRoot p) →+*
      AdjoinRoot (p.map (PowerSeries.C : k →+* PowerSeries k)) :=
  Polynomial.localizeAtOriginEval₂
    (map (PowerSeries.C : k →+* PowerSeries k) p (p.map PowerSeries.C) dvd_rfl)
    (powerSeriesRoot_X_mem_maximalIdeal p)

/-- The actual local map preserves evaluation of all original polynomials. -/
theorem originToPowerSeries_algebraMap (q : (AdjoinRoot p)[X]) :
    originToPowerSeries p
        (algebraMap (AdjoinRoot p)[X] (localRingAtOrigin (AdjoinRoot p)) q) =
      q.eval₂ (map (PowerSeries.C : k →+* PowerSeries k) p
        (p.map PowerSeries.C) dvd_rfl) (of _ PowerSeries.X) :=
  Polynomial.localizeAtOriginEval₂_algebraMap _ _ q

/-- The actual original origin coordinate maps to the original power-series parameter. -/
theorem originToPowerSeries_X :
    originToPowerSeries p
        (algebraMap (AdjoinRoot p)[X] (localRingAtOrigin (AdjoinRoot p)) X) =
      of (p.map (PowerSeries.C : k →+* PowerSeries k)) PowerSeries.X :=
  Polynomial.localizeAtOriginEval₂_X _ _

instance : IsLocalHom (originToPowerSeries p) :=
  Polynomial.isLocalHom_localizeAtOriginEval₂ _ _

/-- The original origin parameter remains a uniformizer in the actual constant root DVR. -/
theorem irreducible_originToPowerSeries_X :
    Irreducible (originToPowerSeries p
      (algebraMap (AdjoinRoot p)[X] (localRingAtOrigin (AdjoinRoot p)) X)) := by
  rw [originToPowerSeries_X]
  apply AdjoinRoot.irreducible_algebraMap ((Fact.out : p.Monic).map _)
    ((Fact.out : p.Monic).irreducible_map_powerSeries_C_residue Fact.out)
  · rw [(Fact.out : p.Monic).natDegree_map]
    exact (Fact.out : Irreducible p).natDegree_pos
  · exact PowerSeries.X_irreducible

/-- The native residue map is literally the identity on the original root field,
when expressed using the two original residue-field identifications. -/
theorem powerSeriesResidueEquiv_comp_residueField_map_originToPowerSeries :
    (powerSeriesResidueEquiv p).toRingHom.comp
        (ResidueField.map (originToPowerSeries p)) =
      (residueFieldAtOriginEquiv (AdjoinRoot p)).symm.toRingHom := by
  apply RingHom.ext
  intro z
  obtain ⟨x, rfl⟩ := (residueFieldAtOriginEquiv (AdjoinRoot p)).surjective z
  change powerSeriesResidueEquiv p
      (ResidueField.map (originToPowerSeries p)
        (residue (localRingAtOrigin (AdjoinRoot p))
          (algebraMap (AdjoinRoot p)[X] (localRingAtOrigin (AdjoinRoot p)) (C x)))) =
    (residueFieldAtOriginEquiv (AdjoinRoot p)).symm
      (residueFieldAtOriginEquiv (AdjoinRoot p) x)
  rw [RingEquiv.symm_apply_apply, ResidueField.map_residue,
    originToPowerSeries_algebraMap, Polynomial.eval₂_C]
  exact powerSeriesResidueEquiv_residue_map_C p x

end AdjoinRoot
