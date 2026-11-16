module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedRawPullbackTrack

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open Scheme.Modules Scheme.Bass Scheme.PolynomialLaurent.GlobalIndex

universe u

namespace ColibTest.SupportedRawPullbackTrack

/-- The underlying chain map is multiplication by the original forward Laurent coordinate. -/
theorem laurent_scalar_component (A : Scheme.QuasiCompactOpenPairs.{u})
    (K : (boundedAboveFlatPerfectSupported A.obj.hom).FullSubcategory) :
    let p := (pairLaurentProjection.app A).hom
    let r := laurentScalar (op A.obj.right)
    (boundedAboveFlatPerfectSupported (pairLaurentFunctor.obj A).obj.hom).ι.map
        ((boundedAboveFlatPerfectSupportedPullbackUnitIso p r).hom.app K) =
      (complexGlobalUnitIso (pairLaurentFunctor.obj A).obj.right r).hom.app
        ((boundedAboveFlatPerfectSupportedPullback p).obj K).obj :=
  boundedAboveFlatPerfectSupportedPullbackUnitIso_hom_original _ _ _

end ColibTest.SupportedRawPullbackTrack
