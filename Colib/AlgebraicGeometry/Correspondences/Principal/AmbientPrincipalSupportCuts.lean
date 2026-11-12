/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Principal.OpenPrincipalSupportCuts
public import Colib.AlgebraicGeometry.Correspondences.Principal.ChartPrincipalSupportCuts

/-! # Original ambient principal support cuts at the actual zero and one endpoints -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow
open AlgebraicGeometry.PrincipalFamilyEndpointCuts

universe u

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

/-- Actual scalar endpoints commute with the original polynomial chart map. -/
@[reassoc (attr := simp)]
theorem endpoint_lineMap {R : Type u} [CommRing R] {C U : Scheme.{u}}
    (p : C ⟶ Spec (.of R)) (u : U ⟶ C) (c : R) :
    endpoint (u ≫ p) c ≫ lineMap p u = u ≫ endpoint p c := by
  apply pullback.hom_ext
  · simp only [Category.assoc, lineMap_projection, endpoint_projection_assoc,
      endpoint_projection, Category.comp_id]
  · simp only [endpoint, lineMap, pullback.map, Category.assoc, pullback.lift_snd,
      Category.comp_id]

/-- The literal endpoint equation is unchanged by the actual polynomial chart. -/
theorem lineMap_endpointEquation {k : Type u} [Field k] {C U : Scheme.{u}}
    (p : C ⟶ Spec (.of k)) (u : U ⟶ C) (c : k) :
    (lineMap p u).appTop (endpointEquation p c) = endpointEquation (u ≫ p) c := by
  rw [endpointEquation, ← PolynomialEndpointFiber.equation_comp]
  simp only [lineMap, pullback.map, pullback.lift_snd, Category.comp_id]

local instance {X Y : Scheme.{u}} (j : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [IsOpenImmersion j] : IsDominant j :=
  ⟨j.isOpenEmbedding.isOpen_range.dense ⟨j (genericPoint X), Set.mem_range_self _⟩⟩

variable {k : Type u} [Field k] {C W U : Scheme.{u}}
    (v : W ⟶ C) [IsOpenImmersion v] [IsIntegral W] [IsIntegral C]
    (p : C ⟶ Spec (.of k)) [IsIntegral (parameterSpace p)]
    [IsLocallyNoetherian (parameterSpace p)]
    (u : U ⟶ C) [IsOpenImmersion u] [IsIntegral U]
    [IsAffine U] [IsNoetherian U] [IsNoetherian (parameterSpace (u ≫ p))]

local instance : IsIntegral (parameterSpace (u ≫ p)) := by
  have : Nonempty (parameterSpace (u ≫ p)) := ⟨endpoint (u ≫ p) 0 (genericPoint U)⟩
  exact isIntegral_of_isOpenImmersion (lineMap p u)

/-- The original ambient principal function and its original global supports have
zero signed cut at zero and the original curve order at one. The chart merely
computes the full quotient lengths; its local fractions are not hypotheses. -/
@[colib_tag "COL-1096"]
theorem ambientPrincipalSupportCuts_zero_one [IsLocallyNoetherian C]
    (f : Γ(W, ⊤)) (hf : f ≠ 0) [Nonempty (ambientUnitOpen p v f)]
    (x : U) (hx : Order.coheight x = 1) :
    let P := parameterSpace p
    let F := ambientRationalFunction p v f
    (∑ᶠ z ∈ principalSupportThrough P (endpoint p 0 (u x)) F,
      (principalCycle P F) z * principalSupportCutLength P (endpoint p 0 (u x)) z
        (endpointEquation p 0)) = 0 ∧
    (∑ᶠ z ∈ principalSupportThrough P (endpoint p 1 (u x)) F,
      (principalCycle P F) z * principalSupportCutLength P (endpoint p 1 (u x)) z
        (endpointEquation p 1)) = C.ord (curveRationalFunction v f) (u x) := by
  have H := chartPrincipalSupportCuts_zero_one v p u f hf x hx
  have hc (c : k) := principalSupportCuts_open (lineMap p u) (endpoint (u ≫ p) c x)
    (ambientRationalFunction p v f) (endpointEquation p c)
  simp only [functionFieldEquiv_openImmersion_eq_schemeFunctionFieldMap,
    lineMap_endpointEquation] at hc
  have he (c : k) : lineMap p u (endpoint (u ≫ p) c x) = endpoint p c (u x) :=
    congrArg (fun a => a x) (endpoint_lineMap p u c)
  simp only [he] at hc
  dsimp only at H ⊢
  rw [← hc 0, ← hc 1]
  refine ⟨H.1, H.2.trans ?_⟩
  rw [← functionFieldEquiv_openImmersion_eq_schemeFunctionFieldMap u]
  exact ord_functionFieldEquiv_openImmersion u _ x

end AlgebraicGeometry.PrincipalFamilyUnitOpen
