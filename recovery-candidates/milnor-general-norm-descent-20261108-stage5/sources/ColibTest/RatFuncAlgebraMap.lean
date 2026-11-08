module

import Colib.FieldTheory.RatFunc.AlgebraMap

open scoped RatFunc
attribute [local instance] Polynomial.algebra

variable {k L : Type*} [Field k] [Field L] [Algebra k L]

-- The actual native scalar structure agrees with coefficient extension, even
-- without finite-dimensionality or algebraicity of the coefficient extension.
example : algebraMap (RatFunc k) (RatFunc L) =
    RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap k L))
      (Polynomial.nonZeroDivisors_le_comap_mapRingHom (algebraMap k L)) :=
  RatFunc.algebraMap_eq_mapRingHom
