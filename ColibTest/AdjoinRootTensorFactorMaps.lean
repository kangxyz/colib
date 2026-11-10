module

import Colib.RingTheory.AdjoinRoot.TensorFactorMaps

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree AdjoinRoot

variable {k : Type*} [Field k] (p h : k[X])
  [Fact (Irreducible p)] [Fact (Irreducible h)]

local notation "E" => AdjoinRoot p
local notation "H" => AdjoinRoot h
local notation "hE" => h.map (algebraMap k E)
local notation "pH" => p.map (algebraMap k H)

variable (q : {q : Σ d : ℕ, MonicIrreducibleOfDegree (AdjoinRoot p) d //
  poly q.2 ∣ h.map (algebraMap k (AdjoinRoot p))})

example (a : E) :
    tensorSwapFactorQuotientEquiv p h q (algebraMap E (AdjoinRoot (poly q.1.2)) a) =
      AdjoinRoot.map (algebraMap k H) p
        (poly (tensorSwapFactorIndexEquiv p h q).1.2)
        (tensorSwapFactorIndexEquiv p h q).2 a :=
  tensorSwapFactorQuotientEquiv_algebraMap p h q a

example (b : H) :
    tensorSwapFactorQuotientEquiv p h q
        (AdjoinRoot.map (algebraMap k E) h (poly q.1.2) q.2 b) =
      algebraMap H (AdjoinRoot (poly (tensorSwapFactorIndexEquiv p h q).1.2)) b :=
  tensorSwapFactorQuotientEquiv_map p h q b

example :
    tensorSwapFactorQuotientEquiv p h q (root (poly q.1.2)) =
      algebraMap H (AdjoinRoot (poly (tensorSwapFactorIndexEquiv p h q).1.2)) (root h) :=
  tensorSwapFactorQuotientEquiv_root p h q

example :
    X - C (algebraMap H (AdjoinRoot (poly (tensorSwapFactorIndexEquiv p h q).1.2))
        (root h)) ∣
      (poly q.1.2).map
        (AdjoinRoot.map (algebraMap k H) p
          (poly (tensorSwapFactorIndexEquiv p h q).1.2)
          (tensorSwapFactorIndexEquiv p h q).2) :=
  tensorSwapFactor_linear_dvd p h q

