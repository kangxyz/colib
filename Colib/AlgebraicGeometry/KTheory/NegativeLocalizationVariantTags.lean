/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterNormalizedBasicOriginalBoundary
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryNegativeBoundarySign
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryNormalizedRowBoundary
public import Colib.Util.References

/-! # Library bindings for the original basic and auxiliary negative localization boundaries -/

@[expose] public section

namespace AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-1264",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
      ParameterNormalizedBasicNegativeBoundary.lean:116-128"
    "adaptation" "Basic normalized to original negative boundary comparison"]
  ParameterNormalizedBasicLocalization.basicNegativeConnecting_eq_original

attribute [colib_tag "COL-1264"]
  ParameterNormalizedBasicLocalization.basicConnecting_original_negative_square

attribute [colib_tag "COL-1264",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
      ParameterAuxiliaryNegativeBoundarySign.lean:102-129"
    "adaptation" "Current auxiliary sign comparison for the literal inverse-image and union opens"]
  ParameterAuxiliaryCurrentFiber.currentNegativeConnecting_eq_original

attribute [colib_tag "COL-1264",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
      ParameterAuxiliaryNormalizedRowBoundary.lean:68-105"
    "adaptation" "Normalized-row auxiliary boundary comparison at the actual signed degree"]
  ParameterAuxiliaryNormalizedRowLocalization.normalizedNegativeConnecting_eq_original

end AlgebraicGeometry.Scheme.Modules
