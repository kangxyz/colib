/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.TwoChartStableSequence

/-!
# Degreewise vanishing for the original spectral Bass row

Vanishing of the two polynomial corners in degree `d` and of the Laurent corner in degree
`d + 1` kills both ends of the genuine spectral Bass row. The conclusion concerns only the
specified degree; it does not assert concentration in a different degree.

Source: `Quillen/KTheory/Bass/TwoChartStableVanishing.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits Topology Topology.LoopPrespectrum
universe u
namespace KTheory.Bass.TwoChartStable

/-- The genuine spectral row vanishes in the indicated degree when its relevant corners do. -/
theorem bassGroup_isZero_of_corners (S : Arrow (Arrow LoopPrespectrum.{u}))
    (hS : SpectralConditions S) (d : ℤ)
    (hplus : IsZero ((stableHomotopyFunctor d).obj S.left.right))
    (hminus : IsZero ((stableHomotopyFunctor d).obj S.right.left))
    (hlaurent : IsZero ((stableHomotopyFunctor (d + 1)).obj S.right.right)) :
    IsZero (bassGroup S d) := by
  have hchart : (chartComplex S d).Exact :=
    ShortComplex.exact_of_isZero_X₂ _ ((biprod_isZero_iff _ _).mpr ⟨hplus, hminus⟩)
  have hright : IsZero (bassRightGroup S d) :=
    bassRightGroup_isZero_of_chart_exact S d
      ((ShortComplex.ab_exact_iff_function_exact _).mp hchart)
  let : Epi (chartDifference S (d + 1)) := hlaurent.epi _
  exact (bassSequence_shortExact S hS d).exact.isZero_of_both_isZero
    (isZero_cokernel_of_epi _) hright

end KTheory.Bass.TwoChartStable
