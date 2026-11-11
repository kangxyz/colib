/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.RetainedZeroSourceChange

/-!
# Flat graph pullback of the literal original section

This specialization requires no supplied zero-ideal comparison. It uses the
actual `pullbackGlobalSections` map and the native equality between the pulled
zero ideal and its comap. The whole finite-flat projection is derived from the
original one, preserving the two actual source and target projections.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Divisors

universe u

namespace AlgebraicGeometry.Cor

open Scheme Scheme.RelativeCurvePencil

variable {k : Type u} [Field k] {S X X' Y : Scheme.{u}}
  (t : S ⟶ Spec (.of k)) [IsSeparated t]
  (q : X ⟶ S) (q' : X' ⟶ S) (r : Y ⟶ S)
  [Smooth (q ≫ t)] [IsSeparated (q ≫ t)] [QuasiCompact (q ≫ t)]
  [Smooth (q' ≫ t)] [IsSeparated (q' ≫ t)] [QuasiCompact (q' ≫ t)]
  [Smooth (r ≫ t)] [IsSeparated (r ≫ t)] [QuasiCompact (r ≫ t)]
  (f : X' ⟶ X) (hf : f ≫ q = q') [Flat f]
  (L : (pullback q r).Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback q r).sheaf.obj
    (pullback q r).ringCatSheaf.property L] (s : Γ(L, ⊤))

local notation "U" => SmoothSite.mk (q ≫ t)
local notation "U'" => SmoothSite.mk (q' ≫ t)
local notation "V" => SmoothSite.mk (r ≫ t)
local notation "g" => retainedSourceChange q q' r f hf
local notation "I" => zeroScheme (pullback q r) L s
local notation "J" => zeroScheme (pullback q' r) ((Modules.pullback g).obj L)
  (pullbackGlobalSections g L s)

variable [IsFinite (I.subschemeι ≫ pullback.fst q r)]
  [Flat (I.subschemeι ≫ pullback.fst q r)]

/-- Finiteness of the literal pulled section's whole zero source. -/
theorem retainedSectionSource_isFinite :
    IsFinite (J.subschemeι ≫ pullback.fst q' r) := by
  rw [zeroScheme_pullback]
  exact retainedSupportSource_isFinite q q' r f hf I

/-- Flatness of the literal pulled section's whole zero source. -/
theorem retainedSectionSource_flat :
    Flat (J.subschemeι ≫ pullback.fst q' r) := by
  rw [zeroScheme_pullback]
  exact retainedSupportSource_flat q q' r f hf I

/-- The source graph acts on the actual original section by literal pullback.
No chosen source isomorphism or correspondence identity is a hypothesis. -/
theorem graph_comp_retainedSection :
    letI := retainedSectionSource_isFinite q q' r f hf L s
    letI := retainedSectionSource_flat q q' r f hf L s
    (graphFunctor k).map (show U' ⟶ U from
        SmoothSite.homMk f (by simp only [← Category.assoc, hf])) ≫
      ofFiniteFlatSpan (X := U) (Y := V)
        (I.subschemeι ≫ pullback.fst q r) (I.subschemeι ≫ pullback.snd q r)
        (by simp only [Category.assoc, pullback.condition_assoc]) =
      ofFiniteFlatSpan (X := U') (Y := V)
        (J.subschemeι ≫ pullback.fst q' r) (J.subschemeι ≫ pullback.snd q' r)
        (by simp only [Category.assoc, pullback.condition_assoc]) := by
  haveI := retainedSectionSource_isFinite q q' r f hf L s
  haveI := retainedSectionSource_flat q q' r f hf L s
  simpa only [zeroScheme_pullback] using graph_comp_retainedSupport t q q' r f hf I

end AlgebraicGeometry.Cor
