module

import Colib.RingTheory.AdjoinRoot.PowerSeriesResidue

noncomputable section

open Polynomial IsLocalRing AdjoinRoot

variable {k : Type*} [Field k] (p : k[X]) [Fact p.Monic] [Fact (Irreducible p)]

local instance : IsLocalRing (AdjoinRoot (p.map (PowerSeries.C : k →+* PowerSeries k))) :=
  isLocalRing_of_irreducible_map_residue ((Fact.out : p.Monic).map _)
    ((Fact.out : p.Monic).irreducible_map_powerSeries_C_residue Fact.out)

local instance : IsLocalHom
    (algebraMap (PowerSeries k) (AdjoinRoot (p.map (PowerSeries.C : k →+* PowerSeries k)))) := by
  rw [AdjoinRoot.algebraMap_eq]
  exact isLocalHom_of_monic ((Fact.out : p.Monic).map _)

example (x : AdjoinRoot p) :
    powerSeriesResidueEquiv p
        (residue (AdjoinRoot (p.map (PowerSeries.C : k →+* PowerSeries k)))
          (map (PowerSeries.C : k →+* PowerSeries k) p (p.map PowerSeries.C) dvd_rfl x)) = x :=
  powerSeriesResidueEquiv_residue_map_C p x

example (a : ResidueField (PowerSeries k)) :
    powerSeriesResidueEquiv p
        (algebraMap (ResidueField (PowerSeries k))
          (ResidueField (AdjoinRoot (p.map (PowerSeries.C : k →+* PowerSeries k)))) a) =
      of p (PowerSeries.residueFieldOfPowerSeries a) :=
  powerSeriesResidueEquiv_algebraMap p a
