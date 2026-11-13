/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.FiniteOpenRestriction
public import Colib.AlgebraicGeometry.Correspondences.Composition.Pushforward
public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.Isomorphism
public import Colib.AlgebraicGeometry.Sites.Smooth.Products

/-!
# Retaining a source coordinate in a target product

The graph of a fixed map out of the source gives a closed immersion of the
actual correspondence ambients. Its finite cycle pushforward retains the
whole support, including the native weights. This construction applies to
an arbitrary smooth retained factor.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open AlgebraicGeometry.Scheme SmoothSite

universe u

namespace AlgebraicGeometry.Cor

variable {k : Type u} [Field k]
  {U V X : SmoothSite (Spec (CommRingCat.of k))}

set_option quotPrecheck false in
local notation "B" => CategoryTheory.Limits.pullback (C := Scheme) U.hom V.hom
local notation "XV" => SmoothSite.product X V
set_option quotPrecheck false in
local notation "B'" => CategoryTheory.Limits.pullback (C := Scheme) U.hom (XV).hom

/-- The ambient closed graph of the original source map in the retained target. -/
def retainSourceGraphMap (r : U ⟶ X) : B ⟶ B' :=
  pullback.lift (pullback.fst U.hom V.hom)
    (pullback.lift (pullback.fst U.hom V.hom ≫ r.left) (pullback.snd U.hom V.hom)
      (by simp only [Category.assoc, MorphismProperty.Over.w, pullback.condition]))
    (by
      rw [SmoothSite.product_hom, ← Category.assoc, pullback.lift_fst,
        Category.assoc, MorphismProperty.Over.w])

@[reassoc]
theorem retainSourceGraphMap_fst (r : U ⟶ X) :
    retainSourceGraphMap (V := V) r ≫ pullback.fst U.hom (XV).hom =
      pullback.fst U.hom V.hom :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem retainSourceGraphMap_snd_fst (r : U ⟶ X) :
    retainSourceGraphMap (V := V) r ≫ pullback.snd U.hom (XV).hom ≫ pullback.fst X.hom V.hom =
      pullback.fst U.hom V.hom ≫ r.left := by
  rw [← Category.assoc]
  unfold retainSourceGraphMap
  rw [pullback.lift_snd, pullback.lift_fst]

@[reassoc]
theorem retainSourceGraphMap_snd_snd (r : U ⟶ X) :
    retainSourceGraphMap (V := V) r ≫ pullback.snd U.hom (XV).hom ≫ pullback.snd X.hom V.hom =
      pullback.snd U.hom V.hom := by
  rw [← Category.assoc]
  unfold retainSourceGraphMap
  rw [pullback.lift_snd, pullback.lift_snd]

instance retainSourceGraphMap_isClosedImmersion (r : U ⟶ X) :
    IsClosedImmersion (retainSourceGraphMap (V := V) r) := by
  let q : B' ⟶ B :=
    pullback.map U.hom (XV).hom U.hom V.hom (𝟙 U.left) (SmoothSite.productSnd X V).left
      (𝟙 _) (by simp) (by simp)
  have : IsSeparated (SmoothSite.productSnd X V).left :=
    inferInstanceAs (IsSeparated (pullback.snd X.hom V.hom))
  have : IsSeparated q :=
    MorphismProperty.pullbackMap (P := @IsSeparated)
      (inferInstance : IsSeparated (𝟙 U.left))
      (inferInstance : IsSeparated (SmoothSite.productSnd X V).left)
      (by simp) (by simp)
  have he : retainSourceGraphMap (V := V) r ≫ q = 𝟙 _ := by
    apply pullback.hom_ext
    · have hq : q ≫ pullback.fst U.hom V.hom = pullback.fst U.hom (XV).hom :=
        (pullback.lift_fst _ _ _).trans (Category.comp_id _)
      rw [Category.assoc, hq, Category.id_comp]
      exact retainSourceGraphMap_fst (V := V) r
    · have hq : q ≫ pullback.snd U.hom V.hom =
          pullback.snd U.hom (XV).hom ≫ pullback.snd X.hom V.hom :=
        pullback.lift_snd _ _ _
      rw [Category.assoc, hq, Category.id_comp]
      exact retainSourceGraphMap_snd_snd (V := V) r
  have : IsClosedImmersion (retainSourceGraphMap (V := V) r ≫ q) := by
    rw [he]
    infer_instance
  exact IsClosedImmersion.of_comp _ q

/-- Push forward a signed correspondence while retaining the given source coordinate. -/
def retainSourceGraph (r : U ⟶ X) :
    (Cor.mk U ⟶ Cor.mk V) →+ (Cor.mk U ⟶ Cor.mk (XV)) where
  toFun a := by
    refine ⟨finiteCyclePushforward (retainSourceGraphMap (V := V) r) a.val, ?_⟩
    apply finiteCyclePushforward_mem_finiteCorrespondences U.hom (XV).hom
      (retainSourceGraphMap (V := V) r) a.val a.property.1
    · intro z hz
      simpa only [Category.assoc, retainSourceGraphMap_fst] using (a.property.2 z hz).1
    · intro z hz
      simpa only [Category.assoc, retainSourceGraphMap_fst] using (a.property.2 z hz).2
  map_zero' := by
    apply Subtype.ext
    exact map_zero (finiteCyclePushforward (retainSourceGraphMap (V := V) r))
  map_add' a b := by
    apply Subtype.ext
    exact map_add (finiteCyclePushforward (retainSourceGraphMap (V := V) r)) a.val b.val

variable {D : Scheme.{u}} (r : U ⟶ X) (p : D ⟶ U.left) (q : D ⟶ V.left)
  (h : p ≫ U.hom = q ≫ V.hom)

/-- The actual target map of the retained finite-flat support. -/
def retainedSpanTarget : D ⟶ (XV).left :=
  pullback.lift (p ≫ r.left) q (by simp only [Category.assoc, MorphismProperty.Over.w, h])

/-- The retained span has the original map to the field. -/
theorem retainedSpanTarget_base : p ≫ U.hom = retainedSpanTarget r p q h ≫ (XV).hom := by
  rw [retainedSpanTarget, SmoothSite.product_hom, ← Category.assoc, pullback.lift_fst,
    Category.assoc, MorphismProperty.Over.w]

/-- The retained span has the actual original paired map followed by the source graph. -/
theorem retainedSpanMap_eq :
    pullback.lift p q h ≫ retainSourceGraphMap (V := V) r =
      pullback.lift p (retainedSpanTarget r p q h) (retainedSpanTarget_base r p q h) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, retainSourceGraphMap_fst, pullback.lift_fst]
  · apply pullback.hom_ext
    · simp only [Category.assoc, retainSourceGraphMap_snd_fst, retainedSpanTarget,
        pullback.lift_fst, pullback.lift_snd]
      exact pullback.lift_fst_assoc p q h r.left
    · simp only [Category.assoc, retainSourceGraphMap_snd_snd, retainedSpanTarget,
        pullback.lift_snd]

/-- On a whole finite-flat span the original left leg is unchanged and the
right leg retains the new coordinate. -/
theorem retainSourceGraph_ofFiniteFlatSpan [IsFinite p] [Flat p] :
    retainSourceGraph r (ofFiniteFlatSpan (X := U) (Y := V) p q h) =
      ofFiniteFlatSpan (X := U) (Y := XV) p (retainedSpanTarget r p q h)
        (retainedSpanTarget_base r p q h) := by
  let : IsNoetherian D := isNoetherian_of_finiteType p
  let m := pullback.lift p q h
  let n := pullback.lift p (retainedSpanTarget r p q h) (retainedSpanTarget_base r p q h)
  let : IsFinite m := isFinite_spanMap p q h
  let : IsFinite n := isFinite_spanMap p (retainedSpanTarget r p q h) _
  apply Subtype.ext
  change finiteCyclePushforward (retainSourceGraphMap (V := V) r)
    (ofFiniteFlatSpan (X := U) (Y := V) p q h).val = _
  rw [ofFiniteFlatSpan_val, ofFiniteFlatSpan_val, finiteCyclePushforward_comp_apply]
  exact finiteCyclePushforward_congr _ _ (retainedSpanMap_eq r p q h) _

/-- Retaining a source coordinate on an ordinary graph is the graph of the paired map. -/
theorem retainSourceGraph_graph (a : U ⟶ V) :
    retainSourceGraph r ((graphFunctor k).map a) =
      (graphFunctor k).map (SmoothSite.productLift r a) := by
  rw [← ofFiniteFlatSpan_id_left a, retainSourceGraph_ofFiniteFlatSpan]
  have ha : retainedSpanTarget r (𝟙 U.left) a.left (by simp) =
      (SmoothSite.productLift r a).left := by
    apply pullback.hom_ext
    · rw [retainedSpanTarget, pullback.lift_fst, Category.id_comp]
      exact (congrArg (fun f => f.left) (SmoothSite.productLift_fst r a)).symm
    · rw [retainedSpanTarget, pullback.lift_snd]
      exact (congrArg (fun f => f.left) (SmoothSite.productLift_snd r a)).symm
  have hbase : (𝟙 U.left) ≫ U.hom = (SmoothSite.productLift r a).left ≫ (XV).hom :=
    (Category.id_comp _).trans (MorphismProperty.Over.w (SmoothSite.productLift r a)).symm
  refine (ofFiniteFlatSpan_eq_of_iso (Iso.refl _) _ _ _ (𝟙 U.left)
    (SmoothSite.productLift r a).left hbase (by simp) ?_).trans
    (ofFiniteFlatSpan_id_left (SmoothSite.productLift r a))
  simpa only [Iso.refl_hom, Category.id_comp] using ha.symm

end AlgebraicGeometry.Cor
