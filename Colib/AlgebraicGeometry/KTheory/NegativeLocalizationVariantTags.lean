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

attribute [colib_tag "COL-1264"]
  ParameterNormalizedBasicLocalization.basicNegativeConnecting_eq_original
  ParameterNormalizedBasicLocalization.basicConnecting_original_negative_square
  ParameterAuxiliaryCurrentFiber.currentNegativeConnecting_eq_original
  ParameterAuxiliaryNormalizedRowLocalization.normalizedNegativeConnecting_eq_original

end AlgebraicGeometry.Scheme.Modules
