/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RetainedSourceChange
public import Colib.AlgebraicGeometry.Correspondences.Graph.WholeFiniteFlatPullback
public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.Isomorphism
public import Colib.AlgebraicGeometry.Scheme.ForgetBaseProduct
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeUnits

/-!
# Flat source graphs and actual retained zero schemes

The whole flat graph theorem is applied to the actual closed paired map from a
retained relative product. The whole-support source-change isomorphism then
identifies the result with the native comapped ideal, retaining both legs.
A separate section comparison derives this ideal from the actual pulled-back
section, including transport through a specified coefficient-line isomorphism.

This replaces the actual source-graph comparison used in
`Motivic/AlgebraicGeometry/Correspondences/Moving/Pencils/SignedSourceEndpoints.lean`
at `a6805c4a87cdfd7717dd7a94039246a167f15380`,
blob `81844c665922764c96de0dd51260c8e7d06c85c5`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Divisors

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {k : Type u} [Field k] {S X X' Y : Scheme.{u}}
  (t : S ⟶ Spec (.of k)) [IsSeparated t]
  (q : X ⟶ S) (q' : X' ⟶ S) (r : Y ⟶ S)
  [Smooth (q ≫ t)] [IsSeparated (q ≫ t)] [QuasiCompact (q ≫ t)]
  [Smooth (q' ≫ t)] [IsSeparated (q' ≫ t)] [QuasiCompact (q' ≫ t)]
  [Smooth (r ≫ t)] [IsSeparated (r ≫ t)] [QuasiCompact (r ≫ t)]
  (f : X' ⟶ X) (hf : f ≫ q = q')

local notation "U" => SmoothSite.mk (q ≫ t)
local notation "U'" => SmoothSite.mk (q' ≫ t)
local notation "V" => SmoothSite.mk (r ≫ t)
local notation "g" => retainedSourceChange q q' r f hf
local notation "φ" => SmoothSite.homMk (X := U') (Y := U) f
  (Eq.trans (Eq.symm (Category.assoc f q t)) (congrArg (fun f₀ => f₀ ≫ t) hf))

omit [Smooth (q ≫ t)] [IsSeparated (q ≫ t)] [QuasiCompact (q ≫ t)]
  [Smooth (r ≫ t)] [IsSeparated (r ≫ t)] [QuasiCompact (r ≫ t)] in
/-- The actual retained zero support is closed in the product over the field. -/
theorem retainedSupport_pair_closed (I : (pullback q r).IdealSheafData) :
    IsClosedImmersion (pullback.lift (I.subschemeι ≫ pullback.fst q r)
      (I.subschemeι ≫ pullback.snd q r)
      (show (I.subschemeι ≫ pullback.fst q r) ≫ (q ≫ t) =
          (I.subschemeι ≫ pullback.snd q r) ≫ (r ≫ t) by
        simp only [Category.assoc, pullback.condition_assoc])) := by
  have hpair : pullback.lift (I.subschemeι ≫ pullback.fst q r)
      (I.subschemeι ≫ pullback.snd q r)
      (show (I.subschemeι ≫ pullback.fst q r) ≫ (q ≫ t) =
          (I.subschemeι ≫ pullback.snd q r) ≫ (r ≫ t) by
        simp only [Category.assoc, pullback.condition_assoc]) =
        I.subschemeι ≫ forgetBaseProductMap t q r := by
    apply pullback.hom_ext <;> simp only [pullback.lift_fst, pullback.lift_snd,
      Category.assoc, forgetBaseProductMap_fst, forgetBaseProductMap_snd]
  rw [hpair]
  infer_instance

variable [hfFlat : Flat f] (I : (pullback q r).IdealSheafData)
  [hIFin : IsFinite (I.subschemeι ≫ pullback.fst q r)]
  [hIFlat : Flat (I.subschemeι ≫ pullback.fst q r)]

/-- Flat source precomposition is the literal comapped support, not a selected
component of that support and not merely its reduced cycle. -/
theorem graph_comp_retainedSupport :
    letI := retainedSupportSource_isFinite q q' r f hf I
    letI := retainedSupportSource_flat q q' r f hf I
    (graphFunctor k).map φ ≫
      ofFiniteFlatSpan (X := U) (Y := V)
        (I.subschemeι ≫ pullback.fst q r) (I.subschemeι ≫ pullback.snd q r)
        (by
          change (I.subschemeι ≫ pullback.fst q r) ≫ (q ≫ t) =
            (I.subschemeι ≫ pullback.snd q r) ≫ (r ≫ t)
          simp only [Category.assoc, pullback.condition_assoc]) =
      ofFiniteFlatSpan (X := U') (Y := V)
        ((I.comap g).subschemeι ≫ pullback.fst q' r)
        ((I.comap g).subschemeι ≫ pullback.snd q' r)
        (by
          change ((I.comap g).subschemeι ≫ pullback.fst q' r) ≫ (q' ≫ t) =
            ((I.comap g).subschemeι ≫ pullback.snd q' r) ≫ (r ≫ t)
          simp only [Category.assoc, pullback.condition_assoc]) := by
  have := retainedSupportSource_isFinite q q' r f hf I
  have := retainedSupportSource_flat q q' r f hf I
  let p : I.subscheme ⟶ (U).left := I.subschemeι ≫ pullback.fst q r
  let s : I.subscheme ⟶ (V).left := I.subschemeι ≫ pullback.snd q r
  let f₀ : U' ⟶ U := φ
  have : IsFinite p := hIFin
  have : Flat p := hIFlat
  have : Flat f₀.left := hfFlat
  have hp : p ≫ (U).hom = s ≫ (V).hom := by
    change (I.subschemeι ≫ pullback.fst q r) ≫ (q ≫ t) =
      (I.subschemeι ≫ pullback.snd q r) ≫ (r ≫ t)
    simp only [Category.assoc, pullback.condition_assoc]
  have : IsClosedImmersion (pullback.lift p s hp) :=
    retainedSupport_pair_closed t q r I
  refine (graph_comp_ofFiniteFlatSpan_of_flat f₀ p s hp).trans ?_
  apply ofFiniteFlatSpan_eq_of_iso (retainedSupportPullbackIso q q' r f hf I)
  · exact retainedSupportPullbackIso_hom_source q q' r f hf I
  · exact retainedSupportPullbackIso_hom_target q q' r f hf I

end AlgebraicGeometry.Cor

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {C D : Scheme.{u}} (g : D ⟶ C) (L : C.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property L]
  (s : Γ(L, ⊤)) (M : D.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible D.sheaf.obj D.ringCatSheaf.property M]
  (e : M ≅ (Modules.pullback g).obj L) (s' : Γ(M, ⊤))

/-- Section-preserving line transport identifies the entire actual zero ideal.
The section equation, rather than just a line isomorphism, is essential here. -/
theorem zeroScheme_eq_comap_of_section_iso
    (hs : e.hom.app ⊤ s' = pullbackGlobalSections g L s) :
    zeroScheme D M s' = (zeroScheme C L s).comap g := by
  rw [← zeroScheme_pullback g L s, ← hs, zeroScheme_congr_iso]

end AlgebraicGeometry.Scheme.RelativeCurvePencil
