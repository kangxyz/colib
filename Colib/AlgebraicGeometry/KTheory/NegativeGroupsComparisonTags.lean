/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassOriginalNegativeNaturality
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedNegativeForgetComparison
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterFiniteNegativeComparison
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatProjectionUnitNaturality
public import Colib.Util.References

/-!
# Bass negative groups and their actual finite-stage comparisons

The tags distinguish the original recursive groups from their finite spectral comparison.
Neither item asserts invertibility of the Bass transitions or the original localization boundary.
-/

@[expose] public section

namespace AlgebraicGeometry.Scheme

attribute [colib_tag "COL-1200"] Bass.negativeKFunctor Bass.supportedNegativeKFunctor
  Bass.negativeKπ Bass.supportedNegativeKπ Bass.supportedNegativeKForgetNat

attribute [colib_ref "ThomasonTrobaugh1990" "Lemma 6.2, pp. 355-356" "background"
  "The recursive two-chart cokernel construction only; no splitting or spectrum identification."]
  Bass.negativeKFunctor Bass.supportedNegativeKFunctor

attribute [colib_ref "WeibelKBook" "III, Definition 4.1" "background"
  "The ring version of the recursive cokernel construction; here the objects are schemes."]
  Bass.negativeKFunctor

namespace Modules

attribute [colib_tag "COL-1201"] boundedAboveFlatCoefficientAmbientNegativeKComparison
  boundedAboveFlatCoefficientAmbientNegativeKComparison_π
  boundedAboveFlatCoefficientAmbientNegativeKComparison_schemeRestriction
  boundedAboveFlatCoefficientSupportedNegativeKComparison
  boundedAboveFlatCoefficientSupportedNegativeKComparison_π
  boundedAboveFlatCoefficientSupportedNegativeKComparison_forget
  GlobalParameterCoefficient.normalizedNegativeKComparison

attribute [colib_ref "quillen"
  "BoundedFlat/CoefficientBassOriginalNegativeComparison.lean:36-78"
  "adaptation" "The actual finite bottom comparison preserves the original Laurent quotient."]
  boundedAboveFlatCoefficientAmbientNegativeKComparison

attribute [colib_tag "COL-1202"] ProductUnitInterchange.doubleProjectionUnitOperation_swap

end Modules
end AlgebraicGeometry.Scheme
