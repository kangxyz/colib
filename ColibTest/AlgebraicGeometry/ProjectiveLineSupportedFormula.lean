module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.SupportedFiveLemma

set_option autoImplicit false

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry

universe u

noncomputable example (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (U : X.Opens) [CompactSpace U.toScheme] (n : ℕ) :
    PerfectSupportedK U.ι n × PerfectSupportedK U.ι n ≃*
      PerfectSupportedK (((projectiveSpaceOver 1 X ↘ X) ⁻¹ᵁ U).ι) n :=
  X.projectiveLineSupportedKEquiv U n

#print axioms AlgebraicGeometry.Scheme.projectiveLineSupportedKEquiv
#print axioms AlgebraicGeometry.Scheme.projectiveLineSupportedKMap_connecting
