/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Colib.AlgebraicGeometry.RelativeCurve.Presentation.OriginalOverlapLifting

/-! Exact first-correction interface, before either second correction or boundary Epi. -/
open AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation
#check retainedCorrectionSquare
#check retainedCorrectionSquare_isPullback
#check retainedCorrectionSquare_etale
#check retainedOverlapToOriginal
#check retainedOverlapToOriginal_etale
#check retainedEtale_original_isPullback
#check retainedToOriginal
#check retainedOriginalOpen
#check retainedOriginalOpen_affine
#check point_mem_retainedOriginalOpen
#check retainedOriginalPullback_isPullback
#check retainedOriginalPullbackIso
#check retainedOriginalPunctureIso
#check refinedGraph_retainedTargetToOriginal
#check originalOverlap_hasRestrictionDifferenceLifting
#check exists_original_overlap_lifting
