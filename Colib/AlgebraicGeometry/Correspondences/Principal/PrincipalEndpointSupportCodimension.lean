/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Principal.PrincipalEndpointSourceCycle
public import Colib.AlgebraicGeometry.Morphisms.Smooth.GenericFiberCodimension

/-! # Original retained source endpoint support has original curve codimension one -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

variable {k : Type u} [Field k] {X C D V : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (q : C ⟶ X) (c : k)

/-- The original source endpoint maps by its original support inclusion and curve
projection, before any finite-image replacement. -/
@[reassoc]
theorem sourceEndpointToCurve_projection (i : D ⟶ parameterSpace (q ≫ p)) :
    sourceEndpointToCurve p q c i =
      pullback.snd (endpoint p c) (i ≫ lineMap p q) ≫ i ≫ projection (q ≫ p) := by
  simp only [sourceEndpointToCurve, polynomialEndpointProjection,
    polynomialEndpointMap_snd_assoc]

/-- The unchanged source endpoint lies over its actual original base point. -/
@[reassoc (attr := simp)]
theorem sourceEndpointToCurve_base (i : D ⟶ parameterSpace (q ≫ p)) :
    sourceEndpointToCurve p q c i ≫ q = pullback.fst (endpoint p c) (i ≫ lineMap p q) := by
  rw [sourceEndpointToCurve_projection]
  have H := congrArg (fun a => a ≫ projection p)
    (pullback.condition (f := endpoint p c) (g := i ≫ lineMap p q))
  simpa only [Category.assoc, lineMap_projection, endpoint_projection, Category.comp_id]
    using H.symm

/-- A genuine retained-support factorization supplies original curve codimension
one at every generic endpoint. Finite dominance is used only for base genericity,
never to infer that the original integral support is flat. -/
theorem sourceEndpoint_generic_original_coheight
    [IsAffine X] [IsIntegral X] [Smooth p]
    (j : V ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
    [IsSeparated (j ≫ q)]
    (i : D ⟶ parameterSpace (q ≫ p)) [IsClosedImmersion i] [IsIntegral D]
    [IsFinite (i ≫ lineMap p q)] [IsDominant (i ≫ lineMap p q)]
    (r : D ⟶ parameterSpace (j ≫ (q ≫ p))) (hr : r ≫ lineMap (q ≫ p) j = i)
    (e : genericPoints (pullback (C := Scheme) (endpoint p c) (i ≫ lineMap p q))) :
    Order.coheight (sourceEndpointToCurve p q c i e.val) = 1 := by
  let l := pullback.snd (endpoint p c) (i ≫ lineMap p q) ≫ r ≫
    projection (j ≫ (q ≫ p))
  have hl : l ≫ j = sourceEndpointToCurve p q c i := by
    rw [sourceEndpointToCurve_projection]
    dsimp only [l]
    rw [Category.assoc, Category.assoc, ← lineMap_projection, ← Category.assoc r, hr]
  have : IsClosedImmersion (l ≫ j) := by rw [hl]; infer_instance
  have : IsClosedImmersion l := IsClosedImmersion.of_comp l j
  have hbase : l ≫ (j ≫ q) = pullback.fst (endpoint p c) (i ≫ lineMap p q) := by
    rw [← Category.assoc, hl, sourceEndpointToCurve_base]
  have : IsFinite (l ≫ (j ≫ q)) := by rw [hbase]; infer_instance
  have hg := polynomialEndpoint_generic_image_generic_of_smooth p (i ≫ lineMap p q) c
    (𝟙 X) (pullback.fst (endpoint p c) (i ≫ lineMap p q)) (by simp) e
  have hx : (j ≫ q) (l e.val) ∈ genericPoints X := by
    change (l ≫ (j ≫ q)) e.val ∈ _
    rw [hbase]
    exact hg
  have H := Scheme.coheight_eq_of_image_mem_genericPoints_finite_closed_support
    l (j ≫ q) 1 e.val hx
  rw [← coheight_eq_of_isOpenImmersion j] at H
  have he := congrArg (fun a => a e.val) hl
  change j (l e.val) = sourceEndpointToCurve p q c i e.val at he
  rwa [he] at H

end AlgebraicGeometry.PrincipalFamilyUnitOpen
