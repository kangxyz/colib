/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.WholeFiniteFlatPullback
public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.Graph
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.RetainSourceGraph

/-!
# Cartesian endpoints of a retained source graph

The paired support remains closed when a source coordinate is retained.
The two endpoint calculations use the same Cartesian zero fiber, with
target maps identified by the actual pullback equation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open AlgebraicGeometry.Scheme SmoothSite SmoothSite.Contraction AffineLineFiber

universe u

namespace AlgebraicGeometry.Cor

variable {k : Type u} [Field k] {U W V X X' : SmoothSite (Spec (CommRingCat.of k))}
  {D : Scheme.{u}}

local notation "γ" => CategoryTheory.Functor.map (graphFunctor k)

private theorem closedSpan_endpoint_congr
    (φ : U ⟶ W) (p₀ p₁ : D ⟶ W.left) [IsFinite p₀] [Flat p₀] [IsFinite p₁] [Flat p₁]
    (q₀ q₁ : D ⟶ V.left) (h₀ : p₀ ≫ W.hom = q₀ ≫ V.hom)
    (h₁ : p₁ ≫ W.hom = q₁ ≫ V.hom) (hp : p₀ = p₁) (hq : q₀ = q₁)
    (e : γ φ ≫ ofFiniteFlatSpan (X := W) (Y := V) p₀ q₀ h₀ =
        ofFiniteFlatSpan (X := U) (Y := V) (pullback.fst φ.left p₀)
          (pullback.snd φ.left p₀ ≫ q₀) (flatWholeSpan_base φ p₀ q₀ h₀)) :
    γ φ ≫ ofFiniteFlatSpan (X := W) (Y := V) p₁ q₁ h₁ =
      ofFiniteFlatSpan (X := U) (Y := V) (pullback.fst φ.left p₁)
        (pullback.snd φ.left p₁ ≫ q₁) (flatWholeSpan_base φ p₁ q₁ h₁) := by
  subst p₁
  subst q₁
  exact e

/-- An actual polynomial face pulls the entire closed finite-flat span back. -/
theorem graph_comp_ofFiniteFlatSpan_of_cartesian_endpoint
    (φ : U ⟶ W) (t : W.left ⟶ Spec (.of (Polynomial k))) [Flat t]
    (a : k) (H : IsPullback φ.left U.hom t (AffineLineFiber.point a))
    (p : D ⟶ W.left) (q : D ⟶ V.left) (h : p ≫ W.hom = q ≫ V.hom)
    [IsFinite p] [Flat p] [IsClosedImmersion (pullback.lift p q h)] :
    γ φ ≫ ofFiniteFlatSpan (X := W) (Y := V) p q h =
      ofFiniteFlatSpan (X := U) (Y := V) (pullback.fst φ.left p)
        (pullback.snd φ.left p ≫ q) (flatWholeSpan_base φ p q h) := by
  let m := pullback.lift p q h
  let p₀ := m ≫ pullback.fst W.hom V.hom
  let q₀ := m ≫ pullback.snd W.hom V.hom
  have hp : p₀ = p := pullback.lift_fst _ _ _
  have hq : q₀ = q := pullback.lift_snd _ _ _
  let : IsFinite p₀ := hp.symm ▸ inferInstanceAs (IsFinite p)
  let : Flat p₀ := hp.symm ▸ inferInstanceAs (Flat p)
  have h₀ : p₀ ≫ W.hom = q₀ ≫ V.hom := by
    simp only [p₀, q₀, Category.assoc, pullback.condition]
  exact closedSpan_endpoint_congr φ p₀ p q₀ q h₀ h hp hq
    (graph_comp_ofFiniteFlatSpan_pair_of_cartesian_endpoint φ m t a H)

/-- Retaining a source map commutes with a Cartesian polynomial face on a closed span. -/
theorem graph_comp_retainSourceGraph_of_cartesian_endpoint
    (φ : U ⟶ W) (t : W.left ⟶ Spec (.of (Polynomial k))) [Flat t]
    (a : k) (H : IsPullback φ.left U.hom t (AffineLineFiber.point a))
    (r : W ⟶ X) (p : D ⟶ W.left) (q : D ⟶ V.left) (h : p ≫ W.hom = q ≫ V.hom)
    [IsFinite p] [Flat p] [IsClosedImmersion (pullback.lift p q h)] :
    γ φ ≫ retainSourceGraph r (ofFiniteFlatSpan (X := W) (Y := V) p q h) =
      retainSourceGraph (φ ≫ r) (γ φ ≫ ofFiniteFlatSpan (X := W) (Y := V) p q h) := by
  let q' := retainedSpanTarget r p q h
  let h' := retainedSpanTarget_base r p q h
  let : IsClosedImmersion (pullback.lift p q' h') := by
    rw [show pullback.lift p q' h' = pullback.lift p q h ≫ retainSourceGraphMap r from
      (retainedSpanMap_eq r p q h).symm]
    infer_instance
  let p₀ := pullback.fst φ.left p
  let q₀ := pullback.snd φ.left p ≫ q
  let h₀ := flatWholeSpan_base φ p q h
  have ht : pullback.snd φ.left p ≫ q' = retainedSpanTarget (φ ≫ r) p₀ q₀ h₀ := by
    apply pullback.hom_ext
    · simp only [q', retainedSpanTarget, Category.assoc, pullback.lift_fst, p₀]
      change pullback.snd φ.left p ≫ p ≫ r.left =
        pullback.fst φ.left p ≫ φ.left ≫ r.left
      rw [pullback.condition_assoc]
    · simp only [q', retainedSpanTarget, Category.assoc, pullback.lift_snd, q₀]
  rw [retainSourceGraph_ofFiniteFlatSpan,
    graph_comp_ofFiniteFlatSpan_of_cartesian_endpoint φ t a H p q' h',
    graph_comp_ofFiniteFlatSpan_of_cartesian_endpoint φ t a H p q h,
    retainSourceGraph_ofFiniteFlatSpan]
  exact ofFiniteFlatSpan_eq_of_iso (Iso.refl _) _ _ _ _ _ _ (by simp)
    (by simpa only [Iso.refl_hom, Category.id_comp] using ht.symm)

/-- The actual native affine section commutes with retaining the source map on a closed span. -/
theorem nativeSection_comp_retainSourceGraph
    (a : k) (r : affineLineCylinder.obj U ⟶ X)
    (p : D ⟶ (affineLineCylinder.obj U).left) (q : D ⟶ V.left)
    (h : p ≫ (affineLineCylinder.obj U).hom = q ≫ V.hom)
    [IsFinite p] [Flat p] [IsClosedImmersion (pullback.lift p q h)] :
    let σ := nativeAffineSection (.of k) U a
    γ σ ≫ retainSourceGraph r (ofFiniteFlatSpan p q h) =
      retainSourceGraph (σ ≫ r) (γ σ ≫ ofFiniteFlatSpan p q h) := by
  let b := Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))
  let e := Scheme.PolynomialSectionPencil.nativeParameterIso (.of k) U
  let t := e.hom ≫ pullback.snd U.hom b
  let : Flat (pullback.snd U.hom b) := Flat.isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback U.hom b) (inferInstanceAs (Flat U.hom))
  let : Flat t := inferInstanceAs (Flat (e.hom ≫ pullback.snd U.hom b))
  exact graph_comp_retainSourceGraph_of_cartesian_endpoint (nativeAffineSection (.of k) U a)
    t a (Scheme.PolynomialSectionPencil.nativeSection_affineLine_isPullback a U) r p q h

/-- Postcomposing the retained coordinate changes the actual right leg of the whole span. -/
theorem retainSourceGraph_comp_productMap_ofFiniteFlatSpan
    (r : U ⟶ X') (f : X' ⟶ X) (p : D ⟶ U.left) (q : D ⟶ V.left)
    (h : p ≫ U.hom = q ≫ V.hom) [IsFinite p] [Flat p] :
    retainSourceGraph r (ofFiniteFlatSpan (X := U) (Y := V) p q h) ≫
        γ (SmoothSite.productMap f (𝟙 V)) =
      retainSourceGraph (r ≫ f) (ofFiniteFlatSpan (X := U) (Y := V) p q h) := by
  rw [retainSourceGraph_ofFiniteFlatSpan, ofFiniteFlatSpan_comp_graph,
    retainSourceGraph_ofFiniteFlatSpan]
  have he : retainedSpanTarget r p q h ≫ (SmoothSite.productMap f (𝟙 V)).left =
      retainedSpanTarget (r ≫ f) p q h := by
    apply pullback.hom_ext
    · change retainedSpanTarget r p q h ≫
          (SmoothSite.productMap f (𝟙 V)).left ≫ (productFst X V).left =
        retainedSpanTarget (r ≫ f) p q h ≫ pullback.fst X.hom V.hom
      have hfst := congrArg (fun u => u.left) (productMap_fst f (𝟙 V))
      change (SmoothSite.productMap f (𝟙 V)).left ≫ (productFst X V).left =
        (productFst X' V).left ≫ f.left at hfst
      rw [hfst]
      change retainedSpanTarget r p q h ≫ pullback.fst X'.hom V.hom ≫ f.left =
        retainedSpanTarget (r ≫ f) p q h ≫ pullback.fst X.hom V.hom
      simp only [retainedSpanTarget, pullback.lift_fst_assoc, pullback.lift_fst, Category.assoc,
        MorphismProperty.Comma.comp_left]
    · change retainedSpanTarget r p q h ≫
          (SmoothSite.productMap f (𝟙 V)).left ≫ (productSnd X V).left =
        retainedSpanTarget (r ≫ f) p q h ≫ pullback.snd X.hom V.hom
      have hsnd := congrArg (fun u => u.left) (productMap_snd f (𝟙 V))
      change (SmoothSite.productMap f (𝟙 V)).left ≫ (productSnd X V).left =
        (productSnd X' V).left ≫ 𝟙 V.left at hsnd
      rw [hsnd, Category.comp_id]
      change retainedSpanTarget r p q h ≫ pullback.snd X'.hom V.hom =
        retainedSpanTarget (r ≫ f) p q h ≫ pullback.snd X.hom V.hom
      simp only [retainedSpanTarget, pullback.lift_snd]
  exact ofFiniteFlatSpan_eq_of_iso (Iso.refl _) _ _ _ _ _ _ (by simp)
    (by simpa only [Iso.refl_hom, Category.id_comp] using he.symm)

end AlgebraicGeometry.Cor
