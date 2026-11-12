/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.TwoChartStableSequence

/-!
Source: `Quillen/KTheory/Bass/TwoChartStableMapInvertibility.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Invertibility of the original spectral Bass row maps

Degreewise isomorphisms at the original chart vertices induce isomorphisms of the original
chart cokernel and right kernel. The latter uses the unchanged span comparison square and
its actual subgroup map, so the subsequent short-five-lemma argument keeps the original maps.
-/
@[expose] public section
noncomputable section
open Topology
open CategoryTheory CategoryTheory.Limits Topology.LoopPrespectrum
universe u
namespace KTheory.Bass.TwoChartStable
variable {S T : Arrow (Arrow LoopPrespectrum.{u})} (a : S ⟶ T) (d : ℤ)

/-- The actual map on the two chart groups is invertible when its two components are. -/
instance chartMap_isIso
    [IsIso ((stableHomotopyFunctor d).map a.left.right)]
    [IsIso ((stableHomotopyFunctor d).map a.right.left)] : IsIso (chartMap a d) := by
  change IsIso (biprod.mapIso
    (asIso ((stableHomotopyFunctor d).map a.left.right))
    (asIso ((stableHomotopyFunctor d).map a.right.left))).hom
  infer_instance

/-- Original chart-vertex isomorphisms induce an isomorphism of the unchanged Laurent quotient.
-/
instance chartCokernelMap_isIso
    [IsIso ((stableHomotopyFunctor d).map a.left.right)]
    [IsIso ((stableHomotopyFunctor d).map a.right.left)]
    [IsIso ((stableHomotopyFunctor d).map a.right.right)] : IsIso (chartCokernelMap a d) := by
  unfold chartCokernelMap
  infer_instance

/-- Original corner and chart isomorphisms induce an isomorphism of the original span quotient.
-/
instance spanCokernelMap_isIso
    [IsIso ((stableHomotopyFunctor d).map a.left.left)]
    [IsIso ((stableHomotopyFunctor d).map a.left.right)]
    [IsIso ((stableHomotopyFunctor d).map a.right.left)] : IsIso (spanCokernelMap a d) := by
  unfold spanCokernelMap
  infer_instance

/-- The actual kernel restriction is invertible under the original quotient and Laurent
isomorphisms. -/
theorem bassRightMap_isIso_of_span
    [IsIso (spanCokernelMap a d)]
    [IsIso ((stableHomotopyFunctor d).map a.right.right)] : IsIso (bassRightMap a d) := by
  suffices h : Function.Bijective (bassRightMap a d) by
    let : Mono (bassRightMap a d) := (AddCommGrpCat.mono_iff_injective _).mpr h.injective
    let : Epi (bassRightMap a d) := (AddCommGrpCat.epi_iff_surjective _).mpr h.surjective
    exact isIso_of_mono_of_epi _
  constructor
  · intro x y h
    apply Subtype.ext
    exact (ConcreteCategory.bijective_of_isIso (spanCokernelMap a d)).injective
      (congrArg Subtype.val h)
  · intro y
    obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso (spanCokernelMap a d)).surjective y.val
    have hz : spanComparison S d x = 0 := by
      apply (ConcreteCategory.bijective_of_isIso
        ((stableHomotopyFunctor d).map a.right.right)).injective
      have he := ConcreteCategory.congr_hom (spanComparison_naturality a d) x
      simp only [ConcreteCategory.comp_apply] at he
      rw [hx, y.property] at he
      exact he.symm.trans (map_zero _).symm
    refine ⟨⟨x, hz⟩, ?_⟩
    exact Subtype.ext hx

/-- Isomorphisms at all original vertices induce an isomorphism of the actual right Bass term.
-/
instance bassRightMap_isIso
    [IsIso ((stableHomotopyFunctor d).map a.left.left)]
    [IsIso ((stableHomotopyFunctor d).map a.left.right)]
    [IsIso ((stableHomotopyFunctor d).map a.right.left)]
    [IsIso ((stableHomotopyFunctor d).map a.right.right)] : IsIso (bassRightMap a d) :=
  bassRightMap_isIso_of_span a d

end KTheory.Bass.TwoChartStable
