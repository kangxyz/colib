module

import Colib.FieldTheory.RatFunc.LaurentMap

open Polynomial

variable {k K : Type*} [Field k] [Field K]

example (φ : k →+* K) (a : k) (x : RatFunc k) :
    RatFunc.laurent (φ a)
        (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ) x) =
      RatFunc.mapRingHom (Polynomial.mapRingHom φ)
        (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ) (RatFunc.laurent a x) :=
  RatFunc.laurent_mapRingHom φ a x

example (a : k) (p : k[X]) :
    (p.map (RatFunc.C : k →+* RatFunc k)).map (RatFunc.laurent a).toRingHom =
      p.map RatFunc.C :=
  RatFunc.map_C_laurent a p
