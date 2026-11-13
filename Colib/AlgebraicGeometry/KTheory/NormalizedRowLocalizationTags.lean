/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryNormalizedRowLocalization
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterNormalizedBasicLocalization

/-!
# Library registration for normalized-row localization

These items concern the actual normalized-row presentations and their prescribed full nulls.
The classical localization theorem is cited as background, not as an additional identification
of the constructed presentations or their class maps.
-/
@[expose] public section

namespace AlgebraicGeometry.Scheme.Modules.ParameterAuxiliaryNormalizedRowLocalization

attribute [colib_tag "COL-0607"] normalizedPresentationLift
  current_normalized_lift_square current_normalized_lift_stable_iff
  normalizedPresentationLift_integer_isStableEquivalence
  normalizedPresentationLift_spec_isStableEquivalence
  normalizedPresentationLift_integer_signed_isIso normalizedPresentationLift_projection

attribute [colib_ref "ThomasonTrobaugh1990" "Theorem 7.4, (7.4.1), p. 365" "background"
  "Classical supported localization; no additional identification of these row presentations."]
  normalizedPresentationLift_integer_isStableEquivalence

end AlgebraicGeometry.Scheme.Modules.ParameterAuxiliaryNormalizedRowLocalization

namespace AlgebraicGeometry.Scheme.Modules.ParameterNormalizedBasicLocalization

attribute [colib_tag "COL-0608"] basicLift auxiliary_basic_lift_square
  auxiliary_basic_lift_stable_iff basicLift_integer_isStableEquivalence
  basicConnecting auxiliary_basic_connecting

attribute [colib_ref "ThomasonTrobaugh1990" "Theorem 7.4, (7.4.1)-(7.4.2), p. 365" "background"
  "Classical basic localization and boundary; the actual row-model class comparison is separate."]
  basicLift_integer_isStableEquivalence

end AlgebraicGeometry.Scheme.Modules.ParameterNormalizedBasicLocalization
