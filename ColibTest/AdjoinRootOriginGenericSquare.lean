module

import Colib.RingTheory.AdjoinRoot.OriginGenericSquare

noncomputable section

open Polynomial Stacks.Chow
open scoped RatFunc
attribute [local instance] Polynomial.algebra

variable {k : Type*} [Field k] (p : k[X]) [Fact p.Monic] [Fact (Irreducible p)]

example :
    (RingHom.comp
      (AdjoinRoot.map (algebraMap (RatFunc k) (LaurentSeries k))
        (p.map (RatFunc.C : k →+* RatFunc k))
        (p.map (algebraMap k (LaurentSeries k))) (by
          rw [Polynomial.map_map, RatFunc.algebraMap_laurentSeries_comp_C]))
      (AdjoinRoot.rationalCoefficientAlgEquiv p (Fact.out : p.Monic)).symm.toRingHom).comp
        (algebraMap (localRingAtOrigin (AdjoinRoot p)) (RatFunc (AdjoinRoot p))) =
      (Stacks.AdjoinRootFraction.toMapAdjoinRoot (LaurentSeries k)
        (p := p.map (PowerSeries.C : k →+* PowerSeries k))
        (q := p.map (algebraMap k (LaurentSeries k))) (by
          rw [Polynomial.map_map]
          rfl)).comp (AdjoinRoot.originToPowerSeries p) :=
  AdjoinRoot.originToPowerSeries_generic_square p

example :
    (AdjoinRoot.rationalCoefficientAlgEquiv p (Fact.out : p.Monic)).symm
        (RatFunc.X : RatFunc (AdjoinRoot p)) =
      AdjoinRoot.of (p.map (RatFunc.C : k →+* RatFunc k)) (RatFunc.X : RatFunc k) :=
  AdjoinRoot.rationalCoefficientAlgEquiv_symm_X p Fact.out

example (q : (AdjoinRoot p)[X]) :
    (RingHom.comp
      (AdjoinRoot.map (algebraMap (RatFunc k) (LaurentSeries k))
        (p.map (RatFunc.C : k →+* RatFunc k))
        (p.map (algebraMap k (LaurentSeries k))) (by
          rw [Polynomial.map_map, RatFunc.algebraMap_laurentSeries_comp_C]))
      (AdjoinRoot.rationalCoefficientAlgEquiv p (Fact.out : p.Monic)).symm.toRingHom)
        (algebraMap (AdjoinRoot p)[X] (RatFunc (AdjoinRoot p)) q) =
      Stacks.AdjoinRootFraction.toMapAdjoinRoot (LaurentSeries k)
        (p := p.map (PowerSeries.C : k →+* PowerSeries k))
        (q := p.map (algebraMap k (LaurentSeries k))) (by
          rw [Polynomial.map_map]
          rfl)
        (q.eval₂ (AdjoinRoot.map (PowerSeries.C : k →+* PowerSeries k) p
          (p.map PowerSeries.C) dvd_rfl) (AdjoinRoot.of _ PowerSeries.X)) :=
  AdjoinRoot.originToPowerSeries_generic_square_polynomial p q
