module

import Colib.RingTheory.AdjoinRoot.OriginToPowerSeries

noncomputable section

open Polynomial IsLocalRing Stacks.Chow

variable {k : Type*} [Field k] (p : k[X]) [Fact p.Monic] [Fact (Irreducible p)]

example : IsLocalHom (AdjoinRoot.originToPowerSeries p) := inferInstance

example : Irreducible (AdjoinRoot.originToPowerSeries p
    (algebraMap (AdjoinRoot p)[X] (localRingAtOrigin (AdjoinRoot p)) X)) :=
  AdjoinRoot.irreducible_originToPowerSeries_X p

local instance : IsLocalRing (AdjoinRoot (p.map (PowerSeries.C : k →+* PowerSeries k))) :=
  AdjoinRoot.isLocalRing_of_irreducible_map_residue ((Fact.out : p.Monic).map _)
    ((Fact.out : p.Monic).irreducible_map_powerSeries_C_residue Fact.out)

example : (AdjoinRoot.powerSeriesResidueEquiv p).toRingHom.comp
    (ResidueField.map (AdjoinRoot.originToPowerSeries p)) =
      (residueFieldAtOriginEquiv (AdjoinRoot p)).symm.toRingHom :=
  AdjoinRoot.powerSeriesResidueEquiv_comp_residueField_map_originToPowerSeries p
