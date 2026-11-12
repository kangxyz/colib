/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Principal.ChartSignedSupportCuts
public import Colib.AlgebraicGeometry.Correspondences.Principal.OriginalPrincipalSupportCuts

/-! # Original principal-cycle support cuts on the actual polynomial chart -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow
open AlgebraicGeometry.PrincipalFamilyUnitOpen

universe u

namespace AlgebraicGeometry.PrincipalFamilyEndpointCuts

variable {k : Type u} [Field k] {W : Scheme.{u}} (p : W ⟶ Spec (.of k))
    [IsIntegral W] [IsNoetherian W]
    [IsIntegral (parameterSpace p)] [IsNoetherian (parameterSpace p)]

omit [IsIntegral W] [IsNoetherian W] in
/-- Genuine section germs reindex the local signed sum by the unchanged global
principal-cycle supports through the endpoint, including signed cancellation. -/
theorem principalSupportCuts_eq_signedEndpointSupportCoefficient
    (c : k) (x : W) (N D : Γ(parameterSpace p, ⊤))
    (hN : W.presheaf.germ ⊤ x (by trivial) ((endpoint p c).appTop N) ≠ 0)
    (hD : W.presheaf.germ ⊤ x (by trivial) ((endpoint p c).appTop D) ≠ 0) :
    let P := parameterSpace p
    let F := P.germToFunctionField ⊤ N / P.germToFunctionField ⊤ D
    (∑ᶠ z ∈ principalSupportThrough P (endpoint p c x) F,
      (principalCycle P F) z * principalSupportCutLength P (endpoint p c x) z
        (endpointEquation p c)) = signedEndpointSupportCoefficient p c x N D := by
  let P := parameterSpace p
  let y := endpoint p c x
  let n := P.presheaf.germ ⊤ y (by trivial) N
  let d := P.presheaf.germ ⊤ y (by trivial) D
  have hn : n ≠ 0 := by
    intro hz
    apply hN
    rw [← endpoint_germ]
    change ((endpoint p c).stalkMap x).hom n = 0
    rw [hz, map_zero]
  have hd : d ≠ 0 := by
    intro hz
    apply hD
    rw [← endpoint_germ]
    change ((endpoint p c).stalkMap x).hom d = 0
    rw [hz, map_zero]
  have H := principalCycle_supportCuts_eq_localPrimeSum P y n d hn hd
    (endpointEquation p c)
  have hfrac : algebraMap (P.presheaf.stalk y) P.functionField n /
      algebraMap (P.presheaf.stalk y) P.functionField d =
      P.germToFunctionField ⊤ N / P.germToFunctionField ⊤ D := by
    rw [P.algebraMap_germ_eq_germToFunctionField (by trivial) N,
      P.algebraMap_germ_eq_germToFunctionField (by trivial) D]
  change (∑ᶠ z ∈ principalSupportThrough P y _,
    (principalCycle P _) z * principalSupportCutLength P y z (endpointEquation p c)) =
      signedEndpointSupportCoefficient p c x N D at H
  rw [hfrac] at H
  exact H

end AlgebraicGeometry.PrincipalFamilyEndpointCuts

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

open AlgebraicGeometry.PrincipalFamilyEndpointCuts

local instance {X Y : Scheme.{u}} (j : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [IsOpenImmersion j] : IsDominant j :=
  ⟨j.isOpenEmbedding.isOpen_range.dense ⟨j (genericPoint X), Set.mem_range_self _⟩⟩

variable {k : Type u} [Field k] {C W U : Scheme.{u}}
    (v : W ⟶ C) [IsOpenImmersion v] [IsIntegral W] [IsIntegral C]
    (p : C ⟶ Spec (.of k)) [IsIntegral (parameterSpace p)]
    (u : U ⟶ C) [IsOpenImmersion u] [IsIntegral U]
    [IsAffine U] [IsNoetherian U] [IsNoetherian (parameterSpace (u ≫ p))]

local instance : IsIntegral (parameterSpace (u ≫ p)) := by
  have : Nonempty (parameterSpace (u ≫ p)) := ⟨endpoint (u ≫ p) 0 (genericPoint U)⟩
  exact isIntegral_of_isOpenImmersion (lineMap p u)

/-- On the original affine chart, the original polynomial function's genuine
principal supports have zero signed endpoint cut at zero and original curve order
at one. All local fractions are produced internally from the original section. -/
@[colib_tag "COL-1092", colib_ref "axiom_stacks_5ed82d14"
  "StacksFrontier/AlgebraicGeometry/Chow/RationalEquivalence/FlatPullbackPrincipalDiviso\
    r.lean:585-627"
  "ingredient" "Original local fraction and order as full quotient-length difference; the \
    support and endpoint assembly is proved here."]
theorem chartPrincipalSupportCuts_zero_one
    (f : Γ(W, ⊤)) (hf : f ≠ 0) [Nonempty (ambientUnitOpen p v f)]
    (x : U) (hx : Order.coheight x = 1) :
    let P := parameterSpace (u ≫ p)
    let F := (lineMap p u).functionFieldMap (ambientRationalFunction p v f)
    (∑ᶠ z ∈ principalSupportThrough P (endpoint (u ≫ p) 0 x) F,
      (principalCycle P F) z * principalSupportCutLength P (endpoint (u ≫ p) 0 x) z
        (endpointEquation (u ≫ p) 0)) = 0 ∧
    (∑ᶠ z ∈ principalSupportThrough P (endpoint (u ≫ p) 1 x) F,
      (principalCycle P F) z * principalSupportCutLength P (endpoint (u ≫ p) 1 x) z
        (endpointEquation (u ≫ p) 1)) =
      U.ord (u.functionFieldMap (curveRationalFunction v f)) x := by
  obtain ⟨a, b, _, hpoly, hcuts⟩ := exists_chartFraction_endpointTor v p u f hf
  obtain ⟨h0, h1, hden, hz, ho⟩ := hcuts x hx
  have H0 := principalSupportCuts_eq_signedEndpointSupportCoefficient (u ≫ p) 0 x
    (numerator (u ≫ p) a b) (denominator (u ≫ p) b) h0 (hden 0)
  have H1 := principalSupportCuts_eq_signedEndpointSupportCoefficient (u ≫ p) 1 x
    (numerator (u ≫ p) a b) (denominator (u ≫ p) b) h1 (hden 1)
  dsimp only at H0 H1 ⊢
  rw [← hpoly] at H0 H1
  constructor
  · exact H0.trans ((signedEndpointSupportCoefficient_eq_weightedTorDifference
      (u ≫ p) 0 x hx _ _ h0 (hden 0)).trans hz)
  · exact H1.trans ((signedEndpointSupportCoefficient_eq_weightedTorDifference
      (u ≫ p) 1 x hx _ _ h1 (hden 1)).trans ho)

end AlgebraicGeometry.PrincipalFamilyUnitOpen
