/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.SupportedOpenFineLocalization

/-!
# Fixed-pair supported fine comparison

The native supported saturated image supplies closure, actual incoming factorization,
approximation and cofinality. Genuine qcqs geometry discharges the geometric inputs.
The boundary is the existing coarse boundary transported along the actual positive
restriction map. No whole-null or prespectrum fiber transport is supplied here.
-/

attribute [colib_ref "quillen"
    "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/SupportedOpenDerivedImage/\
      Factorization.lean:43-201"
    "adaptation"
    "Actual supported cospans and two homotopy pullbacks, strict equations and actual kernels; \
      native support and generic denominator lemmas replace Aglib"]
  AlgebraicGeometry.Scheme.Modules.SupportedOpenDerivedImage.exists_dual_factorization

attribute [colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/GlobalCofinality.lean:40-96"
    "adaptation"
    "Actual supported restriction maps; union compactness suffices without compact U; \
      generic native approximation and cofinality discharge all categorical inputs"]
  AlgebraicGeometry.Scheme.Modules.perfectSupportedOpenKRestrict_succ_bijective_of_union_compact
  AlgebraicGeometry.Scheme.Modules.perfectSupportedOpenKRestrict_injective_of_union_compact
  AlgebraicGeometry.Scheme.Modules.perfectSupportedOpenKEquivOfUnionCompact
  AlgebraicGeometry.Scheme.Modules.perfectSupportedOpenKZeroImageEquivOfUnionCompact

attribute [colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/GlobalLocalization.lean:40-164"
    "adaptation"
    "Fixed-pair native fine range/kernel sequence including K1 to K0; support-forgetting \
      naturality and coherent prespectrum transport are not asserted"]
  AlgebraicGeometry.Scheme.Modules.perfectSupportedConnectingHomOfUnionCompact
  AlgebraicGeometry.Scheme.Modules.perfectSupported_positiveLongExactSequence_of_union_compact
  AlgebraicGeometry.Scheme.Modules.perfectSupported_zeroTail_of_union_compact
  AlgebraicGeometry.Scheme.Modules.perfectSupportedConnectingHomOfUnionCompact_unique

attribute [colib_tag "COL-0334"]
  AlgebraicGeometry.Scheme.Modules.SupportedOpenDerivedImage.exists_dual_factorization
  AlgebraicGeometry.Scheme.Modules.perfectSupportedOpenKRestrict_succ_bijective_of_union_compact
  AlgebraicGeometry.Scheme.Modules.perfectSupportedOpenKZeroImageEquivOfUnionCompact
  AlgebraicGeometry.Scheme.Modules.perfectSupported_zeroTail_of_union_compact
