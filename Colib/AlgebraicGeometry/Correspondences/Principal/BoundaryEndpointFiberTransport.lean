/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Principal.BoundaryGraphEndpointPushforward
public import Colib.AlgebraicGeometry.Correspondences.Principal.PolynomialEndpointFiberMap

/-! # Actual original principal support endpoint transport -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.PrincipalFamilyUnitOpen

attribute [local instance] Classical.propDecidable

universe u

namespace Stacks.Chow.PrincipalBoundary

variable {k : Type u} [Field k] {C X Y V : Scheme.{u}}
    [IsIntegral C] [IsNoetherian C] [IsIntegral X] [IsAffine X]
    (p : X ⟶ Spec (.of k)) (h : Y ⟶ Spec (.of k))
    [IsSeparated p] [IsSeparated h] [Smooth p] [Smooth h]
    (q : C ⟶ parameterSpace p) [IsProper q]
    (j : V ⟶ C) [IsOpenImmersion j] [V.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (j ≫ q)]
    (U : C.Opens) [Nonempty U] (hU : (Set.range j)ᶜ ⊆ (U : Set C))
    (F : Γ(C, U)) (hF : IsUnit F)
    (g : V ⟶ Y) (hg : j ≫ q ≫ (projection p ≫ p) = g ≫ h)

local instance : IsAffineHom (projection p) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @IsAffineHom) (IsPullback.of_hasPullback _ _).flip inferInstance

local instance : IsAffine (parameterSpace p) := isAffine_of_isAffineHom (projection p)

local instance : Smooth (projection p) := by
  have := PrincipalFamilyEndpointCuts.projection_smoothOfRelativeDimension p
  exact SmoothOfRelativeDimension.smooth 1 _

omit [IsSeparated p] [Smooth p] in
/-- The original principal image projection is finite and dominant over the
actual original affine cylinder, with no flatness assertion on its support. -/
theorem imagePoint_projection_isDominant (z : support U F) :
    IsDominant ((integralComponentAt
      (imagePoint (projection p ≫ p) h q j U hU F hF g hg z)).subschemeι ≫
        pullback.fst (projection p ≫ p) h) := by
  let : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, by trivial⟩⟩
  let : IsDomain Γ(X, ⊤) := IsIntegral.component_integral ⊤
  let : Nonempty (parameterSpace p) := ⟨endpoint p 0 (genericPoint X)⟩
  let : IsIntegral (parameterSpace p) :=
    isIntegral_of_isOpenImmersion (affinePolynomialIso p).inv
  let w := imagePoint (projection p ≫ p) h q j U hU F hF g hg z
  let n := (integralComponentAt w).subschemeι ≫ pullback.fst (projection p ≫ p) h
  have hn : Set.range n = Set.univ := by
    simpa only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] using
      (imagePoint_admissible (projection p ≫ p) h q j U hU F hF g hg z).2
  refine ⟨?_⟩
  change Dense (Set.range n)
  rw [hn]
  exact dense_univ

omit [IsSeparated p] in
/-- The original signed principal full-cut weights pass through the canonical
source endpoint map and the original outer graph map, preserving both residue
factors and every collision. All finiteness and dominance are produced internally. -/
theorem componentMap_endpoint_source_fibres (z : support U F) (c : k)
    (y : pullback (C := Scheme) p h) :
    let D := (integralComponentAt z.val).subscheme
    letI := isIntegral_integralComponentAt z.val
    let w := imagePoint (projection p ≫ p) h q j U hU F hF g hg z
    let r := componentMap (projection p ≫ p) h q j U hU F hF g hg z
    let e : D ⟶ (integralComponentAt w).subscheme := integralImageMap r
    let n := (integralComponentAt w).subschemeι ≫ pullback.fst (projection p ≫ p) h
    let v := correspondenceGraphFiberMap p (projection p ≫ p) h w (endpoint p c) (by simp)
    let a := polynomialEndpointMap p n e c
    let s := PolynomialEndpointFiber.equation
      (n ≫ pullback.snd p (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))) c
    let L : D → ℤ := fun x => (cycle U F) z.val *
      ((Module.length (D.presheaf.stalk x)
        (D.presheaf.stalk x ⧸ Ideal.span
          {D.presheaf.germ ⊤ x (by trivial) (e.appTop s)})).toNat : ℤ)
    (∑ᶠ x : genericPoints (pullback (C := Scheme) (endpoint p c) (e ≫ n)),
      if v (a x.val) = y then L (pullback.snd (endpoint p c) (e ≫ n) x.val) *
        ((a ≫ v).residueDegree x.val : ℤ) else 0) =
    ∑ᶠ t : (Σ t : genericPoints (correspondenceGraphFiber (projection p ≫ p) h w
      (endpoint p c)), {x : D // e x = pullback.snd (endpoint p c) n t.val}),
      if v t.1.val = y then L t.2.val *
        ((r.residueDegree t.2.val : ℤ) * (v.residueDegree t.1.val : ℤ)) else 0 := by
  let := isIntegral_integralComponentAt z.val
  dsimp only
  let w := imagePoint (projection p ≫ p) h q j U hU F hF g hg z
  let r := componentMap (projection p ≫ p) h q j U hU F hF g hg z
  let e : (integralComponentAt z.val).subscheme ⟶ (integralComponentAt w).subscheme :=
    integralImageMap r
  let n := (integralComponentAt w).subschemeι ≫ pullback.fst (projection p ≫ p) h
  let v := correspondenceGraphFiberMap p (projection p ≫ p) h w (endpoint p c) (by simp)
  let : IsFinite r := componentMap_isFinite (projection p ≫ p) h q j U hU F hF g hg z
  let : IsFinite e := integralImageMap_isFinite r
  let : IsDominant e := integralImageMap_isDominant r
  let : IsFinite n := (imagePoint_admissible (projection p ≫ p) h q j U hU F hF g hg z).1
  let : IsDominant n := imagePoint_projection_isDominant p h q j U hU F hF g hg z
  have H := polynomialEndpoint_finsum_source_fibres p n e c v
    (fun x => (cycle U F) z.val *
      ((Module.length ((integralComponentAt z.val).subscheme.presheaf.stalk x)
        ((integralComponentAt z.val).subscheme.presheaf.stalk x ⧸ Ideal.span
          {(integralComponentAt z.val).subscheme.presheaf.germ ⊤ x (by trivial)
            (e.appTop (PolynomialEndpointFiber.equation
              (n ≫ pullback.snd p (Spec.map (CommRingCat.ofHom
                (Polynomial.C : k →+* Polynomial k)))) c))})).toNat : ℤ)) y
  have hedeg (x) : e.residueDegree x = r.residueDegree x :=
    integralImageMap_residueDegree r x
  simp only [hedeg] at H
  exact H

end Stacks.Chow.PrincipalBoundary
