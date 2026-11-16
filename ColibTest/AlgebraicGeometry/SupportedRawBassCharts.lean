module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedRawBassCharts
public import Colib.AlgebraicGeometry.Morphisms.OpenImmersion.Pair.Support

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum
open Scheme.Bass Scheme.Modules.SupportedRawBass
open scoped AlgebraicGeometry Topology unitInterval

universe u

namespace ColibTest.SupportedRawBassCharts

/-- The positive normalized boundary is preserved as an entire homotopy. -/
theorem positive_normalized_boundary (A : Scheme.QuasiCompactOpenPairs.{u}) :
    (plusComparison A).at 0 = plusNormalizedHomotopy A :=
  Homotopy.RelHomotopy.at_zero _

/-- The inverse split boundary is preserved as an entire homotopy. -/
theorem inverse_split_boundary (A : Scheme.QuasiCompactOpenPairs.{u}) :
    (minusComparison A).at 1 = minusHomotopy A :=
  Homotopy.RelHomotopy.at_one _

/-- The actual polynomial target row retains the unlocalized point-set seed. -/
def polynomialTargetSeed {U X : Scheme.{u}} (j : U ⟶ X) [CompactSpace U] (T : X.Opens) :
    let B : Scheme.QuasiCompactOpenPairs.{u} :=
      ⟨Scheme.supportOpenPair (j ⁻¹ᵁ T), (by change CompactSpace U; infer_instance)⟩
    let A := pairPolynomialFunctor.obj B
    rawSpectrum A.obj ⟶ parameterLooping (mappingCone (comparison A)) :=
  transition _

/-- Nested Laurent/polynomial source charts keep their complete relative comparison. -/
def nestedSourceTriangle {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [CompactSpace X] (T : X.Opens) :
    let B : Scheme.QuasiCompactOpenPairs.{u} :=
      ⟨Scheme.supportOpenPair (T ⊔ j.opensRange), (by change CompactSpace X; infer_instance)⟩
    let A := pairLaurentFunctor.obj (pairPolynomialFunctor.obj B)
    (plusNormalizedHomotopy A).RelHomotopy (plusHomotopy A) :=
  plusComparison _

end ColibTest.SupportedRawBassCharts
