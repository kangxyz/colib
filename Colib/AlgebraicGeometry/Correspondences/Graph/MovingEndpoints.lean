/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.RetainedGraphSpan
public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.Graph
public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.Isomorphism
public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.RelativeIdealProduct
public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.RelativeSupport
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.AffineComparison

/-!
# Moving endpoints from whole ideal supports

The first endpoint is the graph after cancelling the pole with its
scheme-theoretic multiplicities. If both endpoint divisors lie in a given
open, their signed difference factors through that open.

Adapted from `Motivic/AlgebraicGeometry/Correspondences/Moving/OneSided/MovingEndpoints.lean`
at `motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
blob `bfd9ea719794339333d60ddda5dbae58d5cf623c`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Divisors

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.RelativeCurvePencil
open _root_.AlgebraicGeometry.Scheme.SmoothSite.Contraction

/-- A graph homotopy whose second endpoint factors through the given open. -/
def HasMovingEndpoints {k : Type u} [Field k]
    {X Y A : SmoothSite (Spec (.of k))} (f : X ⟶ Y) (j : A ⟶ Y) : Prop :=
  ∃ β : Cor.mk X ⟶ Cor.mk A,
  ∃ α : Cor.mk (affineLineCylinder.obj X) ⟶ Cor.mk Y,
    (graphFunctor k).map (nativeAffineSection (.of k) X 0) ≫ α = (graphFunctor k).map f ∧
    (graphFunctor k).map (nativeAffineSection (.of k) X 1) ≫ α = β ≫ (graphFunctor k).map j

variable {k : Type u} [Field k] {S X Y : Scheme.{u}}
  (t : S ⟶ Spec (.of k)) [IsSeparated t] (q : X ⟶ S) (r : Y ⟶ S)
  [Smooth (q ≫ t)] [IsSeparated (q ≫ t)] [QuasiCompact (q ≫ t)]
  [Smooth (r ≫ t)] [IsSeparated (r ≫ t)] [QuasiCompact (r ≫ t)]
  [IsSeparated r] [SmoothOfRelativeDimension 1 r]
  (f : X ⟶ Y) (hf : f ≫ r = q)

local notation "U" => SmoothSite.mk (q ≫ t)
local notation "W" => SmoothSite.mk (r ≫ t)
local notation "G" => relativeGraphIdeal q r f hf

variable (A₀ A₁ B : (pullback q r).IdealSheafData)
  [IsFinite (A₀.subschemeι ≫ pullback.fst q r)] [Flat (A₀.subschemeι ≫ pullback.fst q r)]
  [IsFinite (A₁.subschemeι ≫ pullback.fst q r)] [Flat (A₁.subschemeι ≫ pullback.fst q r)]
  [IsFinite (B.subschemeι ≫ pullback.fst q r)] [Flat (B.subschemeι ≫ pullback.fst q r)]

set_option maxHeartbeats 800000 in
-- Elaborating the graph comparison checks both constructed smooth-site structure maps.
/-- The signed ideal-support endpoints of a whole pencil give the actual
graph at zero and a correspondence through the prescribed open at one. -/
theorem hasMovingEndpoints_of_retainedIdealSpans
    {V : SmoothSite (Spec (.of k))} (j : V ⟶ W) [IsOpenImmersion j.left]
    (hb : IsEffectiveCartierDivisor B) (hprod : A₀ = G * B)
    (haV : Set.range (A₁.subschemeι ≫ pullback.snd q r) ⊆ Set.range j.left)
    (hbV : Set.range (B.subschemeι ≫ pullback.snd q r) ⊆ Set.range j.left)
    (α : Cor.mk (affineLineCylinder.obj U) ⟶ Cor.mk W)
    (hZero : (graphFunctor k).map (nativeAffineSection (.of k) U 0) ≫ α =
      retainedIdealSpan (k := k) t q r A₀ - retainedIdealSpan (k := k) t q r B)
    (hOne : (graphFunctor k).map (nativeAffineSection (.of k) U 1) ≫ α =
      retainedIdealSpan (k := k) t q r A₁ - retainedIdealSpan (k := k) t q r B) :
    HasMovingEndpoints (k := k)
      (SmoothSite.homMk (X := U) (Y := W) f
        ((Category.assoc f r t).symm.trans (congrArg (fun g => g ≫ t) hf))) j := by
  have : IsFinite ((G).subschemeι ≫ pullback.fst q r) := by
    rw [← relativeGraphSupportIso_hom_base]
    infer_instance
  have : Flat ((G).subschemeι ≫ pullback.fst q r) := by
    rw [← relativeGraphSupportIso_hom_base]
    infer_instance
  let ga := IsOpenImmersion.lift j.left (A₁.subschemeι ≫ pullback.snd q r) haV
  let gb := IsOpenImmersion.lift j.left (B.subschemeι ≫ pullback.snd q r) hbV
  have hga : ga ≫ j.left = A₁.subschemeι ≫ pullback.snd q r :=
    IsOpenImmersion.lift_fac _ _ _
  have hgb : gb ≫ j.left = B.subschemeι ≫ pullback.snd q r :=
    IsOpenImmersion.lift_fac _ _ _
  have liftedLegs (I : (pullback q r).IdealSheafData) (g : I.subscheme ⟶ V.left)
      (hg : g ≫ j.left = I.subschemeι ≫ pullback.snd q r) :
      (I.subschemeι ≫ pullback.fst q r) ≫ (U).hom = g ≫ V.hom := by
    calc
      _ = (I.subschemeι ≫ pullback.snd q r) ≫ (W).hom :=
        relativeSupport_legs_over_base q r t I
      _ = (g ≫ j.left) ≫ (W).hom := congrArg (fun a => a ≫ (W).hom) hg.symm
      _ = g ≫ V.hom := (Category.assoc g j.left (W).hom).trans
        (congrArg (fun a => g ≫ a) (MorphismProperty.Over.w j))
  have ba := liftedLegs A₁ ga hga
  have bb := liftedLegs B gb hgb
  have span_eq (I : (pullback q r).IdealSheafData)
      [IsFinite (I.subschemeι ≫ pullback.fst q r)] [Flat (I.subschemeι ≫ pullback.fst q r)] :
      retainedIdealSpan (k := k) t q r I =
        ofFiniteFlatSpan (k := k) (X := U) (Y := W) (I.subschemeι ≫ pullback.fst q r)
          (I.subschemeι ≫ pullback.snd q r) (relativeSupport_legs_over_base q r t I) := rfl
  refine ⟨ofFiniteFlatSpan (k := k) (X := U) (Y := V) _ ga ba -
    ofFiniteFlatSpan (k := k) (X := U) (Y := V) _ gb bb, α, ?_, ?_⟩
  · rw [hZero,
      retainedSpan_add_of_ideal_product (k := k) t q r G B A₀
        (isLocallyPrincipal_of_isEffectiveCartierDivisor G inferInstance) hb hprod,
      add_sub_cancel_right, span_eq G]
    let a : U ⟶ W := SmoothSite.homMk f
      ((Category.assoc f r t).symm.trans (congrArg (fun g => g ≫ t) hf))
    have hG : ((G).subschemeι ≫ pullback.fst q r) ≫ (U).hom =
        ((G).subschemeι ≫ pullback.snd q r) ≫ (W).hom :=
      relativeSupport_legs_over_base q r t G
    exact ofFiniteFlatSpan_relativeGraph (k := k) («U» := U) («W» := W) q r f hf a rfl hG
  · have liftSpan {D : Scheme.{u}} (f' : D ⟶ (U).left) [IsFinite f'] [Flat f']
        (g : D ⟶ V.left) (g' : D ⟶ (W).left) (hg : g ≫ j.left = g')
        (h : f' ≫ (U).hom = g ≫ V.hom) (h' : f' ≫ (U).hom = g' ≫ (W).hom) :
        ofFiniteFlatSpan (k := k) (X := U) (Y := V) f' g h ≫ (graphFunctor k).map j =
          ofFiniteFlatSpan (k := k) (X := U) (Y := W) f' g' h' := by
      refine (ofFiniteFlatSpan_comp_graph (k := k) (X := U) (Y := V) (Z := W) f' g h j).trans ?_
      apply ofFiniteFlatSpan_eq_of_iso (k := k) (X := U) (Y := W) (Iso.refl _)
      · exact Category.id_comp _
      · exact (Category.id_comp _).trans hg.symm
    rw [hOne, span_eq A₁, span_eq B, Preadditive.sub_comp,
      liftSpan _ ga _ hga ba (relativeSupport_legs_over_base q r t A₁),
      liftSpan _ gb _ hgb bb (relativeSupport_legs_over_base q r t B)]

end AlgebraicGeometry.Cor
