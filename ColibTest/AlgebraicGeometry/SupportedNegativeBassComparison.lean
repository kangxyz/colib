/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterSupportedCurrentStageRange

/-! Check the original supported Bass groups in the independently defined current telescope. -/

open AlgebraicGeometry.Scheme.Modules.GlobalSupportedParameterCoefficient

#check currentStageInclusion_isIso_of_le
#check currentNegativeKComparison
#check currentNegativeKComparison_π
#print axioms currentStageInclusion_isIso_of_le
#print axioms currentNegativeKComparison
#print axioms currentNegativeKComparison_π
