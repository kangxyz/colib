module

import Colib.AlgebraicGeometry.ProjectiveLine.RootChartInversion

open Polynomial AlgebraicGeometry

variable {k : Type*} [Field k]

example (p : k[X]) :
    (p.map (RatFunc.C : k →+* RatFunc k)).map
      (projectiveLineChartInversion k).toRingHom = p.map RatFunc.C :=
  map_ratFunc_C_chartInversion p

example (p : k[X]) [Fact (Irreducible p)] (hp : p.Monic)
    (x : AdjoinRoot (p.map (RatFunc.C : k →+* RatFunc k))) :
    AdjoinRoot.rationalCoefficientAlgEquiv p hp
      (AdjoinRoot.map (projectiveLineChartInversion k).toRingHom
        (p.map RatFunc.C) (p.map RatFunc.C)
        (by rw [map_ratFunc_C_chartInversion]; exact dvd_rfl) x) =
      projectiveLineChartInversion (AdjoinRoot p)
        (AdjoinRoot.rationalCoefficientAlgEquiv p hp x) :=
  rationalCoefficientAlgEquiv_map_chartInversion p hp x
