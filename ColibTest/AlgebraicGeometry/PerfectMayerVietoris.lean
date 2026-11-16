module

public import Colib.AlgebraicGeometry.KTheory.PerfectMayerVietorisZero
public import Colib.AlgebraicGeometry.KTheory.SupportedMayerVietoris

set_option autoImplicit false

open CategoryTheory CategoryTheory.Waldhausen AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry

universe u

namespace ColibTest

example {V X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace V] [QuasiSeparatedSpace V] (j : V ⟶ X) [IsOpenImmersion j]
    (T : X.Opens) [CompactSpace T.toScheme]
    (hc : ∀ x : X, x ∈ Set.range j ∨ x ∈ T) :
    (PerfectMayerVietoris.restrictionPair j T 0).range =
      (PerfectMayerVietoris.overlapDifference j T 0).ker :=
  PerfectMayerVietoris.range_restrictionPair_eq_ker_overlapDifference_zero j T hc

example {V X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace V] [QuasiSeparatedSpace V] (j : V ⟶ X) [IsOpenImmersion j]
    (T Z : X.Opens) [CompactSpace T.toScheme] [CompactSpace (j ⁻¹ᵁ T).toScheme]
    (hc : ∀ x : X, x ∈ Set.range j ∨ x ∈ T) (hZ : IsCompact (Z : Set X)) (n : ℕ) :
    Function.MulExact (SupportedMayerVietoris.restrictionPair j T Z n)
      (SupportedMayerVietoris.overlapDifference j T Z n) :=
  (SupportedMayerVietoris.fiveTerm_exact j T Z hc hZ n).2.2

#print axioms PerfectMayerVietoris.fiveTerm_exact
#print axioms SupportedMayerVietoris.fiveTerm_exact
#print axioms SupportedMayerVietoris.fineConnecting_natural

end ColibTest
