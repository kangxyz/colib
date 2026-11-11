/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.Isomorphism
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeGraphDivisor

/-!
# The whole retained relative graph span is the existing graph correspondence

The comparison uses the actual whole graph-support isomorphism and both
original coordinate equations. It requires no integral or connected source.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Divisors

universe u

namespace AlgebraicGeometry.Cor

open Scheme Scheme.RelativeCurvePencil

variable {k : Type u} [Field k] {S X V : Scheme.{u}}
  (t : S ⟶ Spec (.of k)) (q : X ⟶ S) (r : V ⟶ S) [IsSeparated r]
  [Smooth (q ≫ t)] [IsSeparated (q ≫ t)] [QuasiCompact (q ≫ t)]
  [Smooth (r ≫ t)] [IsSeparated (r ≫ t)] [QuasiCompact (r ≫ t)]
  (φ : X ⟶ V) (hφ : φ ≫ r = q)

local notation "U" => SmoothSite.mk (q ≫ t)
local notation "W" => SmoothSite.mk (r ≫ t)
local notation "I" => relativeGraphIdeal q r φ hφ

/-- The entire retained graph span is the native graph, with the actual target map. -/
theorem ofFiniteFlatSpan_relativeGraph :
    letI : IsFinite (I.subschemeι ≫ pullback.fst q r) := by
      rw [← relativeGraphSupportIso_hom_base]
      infer_instance
    letI : Flat (I.subschemeι ≫ pullback.fst q r) := by
      rw [← relativeGraphSupportIso_hom_base]
      infer_instance
    ofFiniteFlatSpan (X := U) (Y := W)
      (I.subschemeι ≫ pullback.fst q r) (I.subschemeι ≫ pullback.snd q r)
      (by simp only [Category.assoc, pullback.condition_assoc]) =
      (graphFunctor k).map (SmoothSite.homMk φ (by simp only [← Category.assoc, hφ])) := by
  haveI : IsFinite (I.subschemeι ≫ pullback.fst q r) := by
    rw [← relativeGraphSupportIso_hom_base]
    infer_instance
  haveI : Flat (I.subschemeι ≫ pullback.fst q r) := by
    rw [← relativeGraphSupportIso_hom_base]
    infer_instance
  rw [← ofFiniteFlatSpan_id_left]
  apply ofFiniteFlatSpan_eq_of_iso (relativeGraphSupportIso q r φ hφ)
  · simpa only [Category.comp_id] using relativeGraphSupportIso_hom_base q r φ hφ
  · exact relativeGraphSupportIso_hom_target q r φ hφ

end AlgebraicGeometry.Cor
