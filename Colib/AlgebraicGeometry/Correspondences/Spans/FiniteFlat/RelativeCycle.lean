/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.CartierCycle
public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.Graph
public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.RelativeSupport
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.ProductBoundary
public import Colib.AlgebraicGeometry.Scheme.ForgetBaseProduct

/-!
# The cycle of a whole relative finite-flat span

The actual span and its graph postcomposition have the whole fundamental
cycle of their zero schemes. Changing the target factor retains the actual
finite map and its residue degrees before forgetting the coefficient base.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {k : Type u} [Field k] {S K V A : Scheme.{u}}
  (t : S ⟶ Spec (.of k)) [IsSeparated t]
  (b : K ⟶ S) (r : V ⟶ S) (r' : A ⟶ S)
  [Smooth (b ≫ t)] [IsSeparated (b ≫ t)] [QuasiCompact (b ≫ t)]
  [Smooth (r ≫ t)] [IsSeparated (r ≫ t)] [QuasiCompact (r ≫ t)]
  [Smooth (r' ≫ t)] [IsSeparated (r' ≫ t)] [QuasiCompact (r' ≫ t)]
  (I : (pullback b r).IdealSheafData)
  [IsFinite (I.subschemeι ≫ pullback.fst b r)] [Flat (I.subschemeι ≫ pullback.fst b r)]

local notation "K₀" => (SmoothSite.mk (b ≫ t))
local notation "V₀" => (SmoothSite.mk (r ≫ t))
local notation "A₀" => (SmoothSite.mk (r' ≫ t))

omit [Smooth (r' ≫ t)] [IsSeparated (r' ≫ t)] [QuasiCompact (r' ≫ t)] in
/-- Forgetting the coefficient base pushes the same entire relative zero cycle
to the absolute correspondence product. -/
theorem ofFiniteFlatSpan_relativeCycle_val [IsNoetherian (pullback b r)] :
    (ofFiniteFlatSpan (X := K₀) (Y := V₀)
      (I.subschemeι ≫ pullback.fst b r) (I.subschemeι ≫ pullback.snd b r)
      (relativeSupport_legs_over_base b r t I)).val =
    finiteCyclePushforward (forgetBaseProductMap t b r) (cartierCycle I) := by
  let : IsNoetherian K := isNoetherian_of_finiteType_of_isNoetherian (b ≫ t)
  let : IsNoetherian I.subscheme := isNoetherian_of_finiteType_of_isNoetherian
    (I.subschemeι ≫ pullback.fst b r)
  let p := I.subschemeι ≫ pullback.fst b r
  let q := I.subschemeι ≫ pullback.snd b r
  let h := relativeSupport_legs_over_base b r t I
  let n := pullback.lift p q h
  let : IsFinite n := isFinite_spanMap (X := K₀) (Y := V₀) p q h
  rw [ofFiniteFlatSpan_val]
  change _ = finiteCyclePushforward (forgetBaseProductMap t b r)
    (finiteCyclePushforward I.subschemeι (AlgebraicCycle.fundamentalCycle I.subscheme))
  rw [finiteCyclePushforward_comp_apply]
  have hn : n = I.subschemeι ≫ forgetBaseProductMap t b r := by
    apply pullback.hom_ext <;>
      simp only [n, p, q, pullback.lift_fst, pullback.lift_snd, Category.assoc,
        forgetBaseProductMap_fst, forgetBaseProductMap_snd]
  exact finiteCyclePushforward_congr n _ hn _

variable (g : V ⟶ A) (hg : g ≫ r' = r) [IsSeparated r']

omit [IsSeparated t] [Smooth (b ≫ t)] [IsSeparated (b ≫ t)] [QuasiCompact (b ≫ t)]
  [Smooth (r ≫ t)] [IsSeparated (r ≫ t)] [QuasiCompact (r ≫ t)]
  [Smooth (r' ≫ t)] [IsSeparated (r' ≫ t)] [QuasiCompact (r' ≫ t)]
  [Flat (I.subschemeι ≫ pullback.fst b r)] in
/-- The actual target factorization of a support finite over the first
projection is a finite map into the retained target product. -/
theorem isFinite_relativeSupportTargetMap :
    IsFinite (I.subschemeι ≫ productSecondMap b r' r g hg.symm) := by
  let m := I.subschemeι ≫ productSecondMap b r' r g hg.symm
  have : IsFinite (m ≫ pullback.fst b r') := by
    simpa only [m, Category.assoc, productSecondMap_fst] using
      (inferInstance : IsFinite (I.subschemeι ≫ pullback.fst b r))
  exact IsFinite.of_comp m (pullback.fst b r')

/-- Graph postcomposition first pushes the entire support along the actual
retained target map, then forgets the relative coefficient base. -/
theorem ofFiniteFlatSpan_relativeCycle_comp_graph_val :
    let u : V₀ ⟶ A₀ := SmoothSite.homMk g (by
      change g ≫ (r' ≫ t) = r ≫ t
      rw [← Category.assoc, hg])
    let m := I.subschemeι ≫ productSecondMap b r' r g hg.symm
    letI : IsFinite m := isFinite_relativeSupportTargetMap b r r' I g hg
    letI : IsNoetherian I.subscheme := by
      let : IsNoetherian K := isNoetherian_of_finiteType_of_isNoetherian (b ≫ t)
      exact isNoetherian_of_finiteType_of_isNoetherian (I.subschemeι ≫ pullback.fst b r)
    (ofFiniteFlatSpan (X := K₀) (Y := V₀)
      (I.subschemeι ≫ pullback.fst b r) (I.subschemeι ≫ pullback.snd b r)
      (relativeSupport_legs_over_base b r t I) ≫ (graphFunctor k).map u).val =
    finiteCyclePushforward (forgetBaseProductMap t b r')
      (finiteCyclePushforward m (AlgebraicCycle.fundamentalCycle I.subscheme)) := by
  let : IsFinite (I.subschemeι ≫ productSecondMap b r' r g hg.symm) :=
    isFinite_relativeSupportTargetMap b r r' I g hg
  let : IsNoetherian K := isNoetherian_of_finiteType_of_isNoetherian (b ≫ t)
  let : IsNoetherian I.subscheme :=
    isNoetherian_of_finiteType_of_isNoetherian (I.subschemeι ≫ pullback.fst b r)
  let p := I.subschemeι ≫ pullback.fst b r
  let q := I.subschemeι ≫ pullback.snd b r
  have h : p ≫ (b ≫ t) = (q ≫ g) ≫ (r' ≫ t) := by
    rw [Category.assoc q g, ← Category.assoc g, hg]
    exact relativeSupport_legs_over_base b r t I
  let n := pullback.lift p (q ≫ g) h
  let : IsFinite n := isFinite_spanMap (X := K₀) (Y := A₀) p (q ≫ g) h
  let u : V₀ ⟶ A₀ := SmoothSite.homMk g (by
    change g ≫ (r' ≫ t) = r ≫ t
    rw [← Category.assoc, hg])
  let h₀ := relativeSupport_legs_over_base b r t I
  change (ofFiniteFlatSpan (X := K₀) (Y := V₀) p q h₀ ≫ (graphFunctor k).map u).val = _
  let β := ofFiniteFlatSpan (X := K₀) (Y := A₀) p (q ≫ g) h
  have hcomp : ofFiniteFlatSpan (X := K₀) (Y := V₀) p q h₀ ≫ (graphFunctor k).map u = β :=
    ofFiniteFlatSpan_comp_graph (X := K₀) (Y := V₀) (Z := A₀) p q h₀ u
  have hn : n = (I.subschemeι ≫ productSecondMap b r' r g hg.symm) ≫
      forgetBaseProductMap t b r' := by
    apply pullback.hom_ext <;>
      simp only [n, p, q, pullback.lift_fst, pullback.lift_snd, Category.assoc,
        forgetBaseProductMap_fst, forgetBaseProductMap_snd,
        productSecondMap_fst, productSecondMap_snd]
  calc
    _ = β.val := congrArg (fun a : Cor.mk K₀ ⟶ Cor.mk A₀ ↦ a.val) hcomp
    _ = finiteCyclePushforward n (AlgebraicCycle.fundamentalCycle I.subscheme) :=
      ofFiniteFlatSpan_val (X := K₀) (Y := A₀) p (q ≫ g) h
    _ = _ := (finiteCyclePushforward_congr n _ hn _).trans
      (finiteCyclePushforward_comp_apply _ _ _).symm

end AlgebraicGeometry.Cor
