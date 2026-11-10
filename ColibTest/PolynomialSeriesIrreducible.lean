module

import Colib.RingTheory.Polynomial.SeriesIrreducible

open Polynomial IsLocalRing

variable {k : Type*} [Field k] (p : k[X]) (hp : p.Monic) (hirr : Irreducible p)

example : Irreducible (p.map (algebraMap k (LaurentSeries k))) :=
  hp.irreducible_map_laurentSeries_C hirr

example : Irreducible ((p.map (PowerSeries.C : k →+* PowerSeries k)).map
    (residue (PowerSeries k))) :=
  hp.irreducible_map_powerSeries_C_residue hirr

example : (((p.map (PowerSeries.C : k →+* PowerSeries k)).map
    (residue (PowerSeries k))).map PowerSeries.residueFieldOfPowerSeries.toRingHom) = p :=
  p.map_powerSeries_C_residueFieldOfPowerSeries
