/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdjoinRoot.ResidueField
public import Colib.RingTheory.Polynomial.SeriesIrreducible

/-!
# The actual residue of the constant power-series root algebra

The residue field of the actual AdjoinRoot of a constant monic irreducible
polynomial over PowerSeries k is identified with the original AdjoinRoot over k.
This composes the native residue-polynomial comparison and native mapRingEquiv;
no closure or residue carrier is introduced. It preserves every original root
field element under the original AdjoinRoot.map, as well as the actual base
residue algebra map. These are the literal maps needed to return the monogenic
DVR norm-residue square to the original constant field.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing

namespace AdjoinRoot

variable {k : Type*} [Field k] (p : k[X]) [Fact p.Monic] [Fact (Irreducible p)]

local instance : IsLocalRing (AdjoinRoot (p.map (PowerSeries.C : k →+* PowerSeries k))) :=
  isLocalRing_of_irreducible_map_residue ((Fact.out : p.Monic).map _)
    ((Fact.out : p.Monic).irreducible_map_powerSeries_C_residue Fact.out)

local instance : IsLocalHom
    (algebraMap (PowerSeries k) (AdjoinRoot (p.map (PowerSeries.C : k →+* PowerSeries k)))) := by
  rw [AdjoinRoot.algebraMap_eq]
  exact isLocalHom_of_monic ((Fact.out : p.Monic).map _)

/-- The actual power-series root algebra's residue field is the original root field. -/
def powerSeriesResidueEquiv :
    ResidueField (AdjoinRoot (p.map (PowerSeries.C : k →+* PowerSeries k))) ≃+* AdjoinRoot p :=
  (residueFieldEquivAdjoinRoot _
    ((Fact.out : p.Monic).irreducible_map_powerSeries_C_residue Fact.out)).trans
    (mapRingEquiv PowerSeries.residueFieldOfPowerSeries
      ((p.map (PowerSeries.C : k →+* PowerSeries k)).map (residue (PowerSeries k))) p
      (by
        change Associated
          ((((p.map (PowerSeries.C : k →+* PowerSeries k)).map
            (residue (PowerSeries k))).map PowerSeries.residueFieldOfPowerSeries.toRingHom)) p
        rw [Polynomial.map_powerSeries_C_residueFieldOfPowerSeries]))

/-- A coefficient's residue is its original constant term in the old root field. -/
theorem powerSeriesResidueEquiv_residue_of (a : PowerSeries k) :
    powerSeriesResidueEquiv p
        (residue (AdjoinRoot (p.map (PowerSeries.C : k →+* PowerSeries k)))
          (of _ a)) = of p (PowerSeries.constantCoeff a) := by
  simp only [powerSeriesResidueEquiv, RingEquiv.trans_apply,
    residueFieldEquivAdjoinRoot_residue_of, coe_mapRingEquiv, map_of]
  rfl

/-- Every original root field element is recovered after the original constant
coefficient map and the actual residue, not only the chosen root or coefficients. -/
theorem powerSeriesResidueEquiv_residue_map_C (x : AdjoinRoot p) :
    powerSeriesResidueEquiv p
        (residue (AdjoinRoot (p.map (PowerSeries.C : k →+* PowerSeries k)))
          (map (PowerSeries.C : k →+* PowerSeries k) p (p.map PowerSeries.C) dvd_rfl x)) = x := by
  have h : ((powerSeriesResidueEquiv p).toRingHom.comp
      (residue (AdjoinRoot (p.map (PowerSeries.C : k →+* PowerSeries k))))).comp
        (map (PowerSeries.C : k →+* PowerSeries k) p (p.map PowerSeries.C) dvd_rfl) =
      RingHom.id (AdjoinRoot p) := by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro a
      change powerSeriesResidueEquiv p (residue _ (map _ _ _ _ (of p a))) = of p a
      rw [map_of, powerSeriesResidueEquiv_residue_of]
      simp
    · change powerSeriesResidueEquiv p
        (residue (AdjoinRoot (p.map (PowerSeries.C : k →+* PowerSeries k)))
          (map (PowerSeries.C : k →+* PowerSeries k) p (p.map PowerSeries.C) dvd_rfl
            (root p))) = root p
      rw [map_root]
      simp only [powerSeriesResidueEquiv, RingEquiv.trans_apply,
        residueFieldEquivAdjoinRoot_residue_root, coe_mapRingEquiv, map_root]
  exact RingHom.congr_fun h x

/-- The original base residue algebra map is carried to its literal coefficient map. -/
theorem powerSeriesResidueEquiv_algebraMap (a : ResidueField (PowerSeries k)) :
    powerSeriesResidueEquiv p
        (algebraMap (ResidueField (PowerSeries k))
          (ResidueField (AdjoinRoot (p.map (PowerSeries.C : k →+* PowerSeries k)))) a) =
      of p (PowerSeries.residueFieldOfPowerSeries a) := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  change powerSeriesResidueEquiv p (residue _ (of _ b)) = of p (PowerSeries.constantCoeff b)
  exact powerSeriesResidueEquiv_residue_of p b

/-- The inverse is exactly the original constant map followed by the actual residue. -/
theorem powerSeriesResidueEquiv_symm (x : AdjoinRoot p) :
    (powerSeriesResidueEquiv p).symm x =
      residue (AdjoinRoot (p.map (PowerSeries.C : k →+* PowerSeries k)))
        (map (PowerSeries.C : k →+* PowerSeries k) p (p.map PowerSeries.C) dvd_rfl x) := by
  apply (powerSeriesResidueEquiv p).injective
  rw [RingEquiv.apply_symm_apply, powerSeriesResidueEquiv_residue_map_C]

end AdjoinRoot
