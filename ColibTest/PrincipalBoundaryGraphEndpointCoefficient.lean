/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Principal.BoundaryGraphEndpointCoefficient

/-! # Actual original signed principal coefficient and native endpoint Tor -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.PrincipalFamilyUnitOpen

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

/-- The actual native local incidence coefficient has the original signed finite
source-cut formula, retaining all source fibre points and their residue degrees. -/
example (z : support U F)
    (c : k) (s : genericPoints X) :
    let w := imagePoint (projection p ≫ p) h q j U hU F hF g hg z
    let D := (integralComponentAt z.val).subscheme
    letI := isIntegral_integralComponentAt z.val
    let r := componentMap (projection p ≫ p) h q j U hU F hF g hg z
    let e := integralImageMap r
    let eqn := PolynomialEndpointFiber.equation
      ((integralComponentAt w).subschemeι ≫ pullback.fst (projection p ≫ p) h ≫
        pullback.snd p (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))) c
    ∀ t : genericPoints (correspondenceIncidence p (projection p ≫ p) h
        (correspondenceGraphMap p (projection p ≫ p) (endpoint p c) (by simp) s.val) w),
      (cycle U F) z.val *
        (∑ᶠ x ∈ e.base ⁻¹' {pullback.snd (C := Scheme) _ _ t.val},
          ((Module.length (D.presheaf.stalk x)
            (D.presheaf.stalk x ⧸ Ideal.span
              {D.presheaf.germ ⊤ x (by trivial) (e.appTop eqn)})).toNat : ℤ) *
                (r.residueDegree x : ℤ)) =
        (componentCorrespondence (projection p ≫ p) h q j U hU F hF g hg z).val w *
          correspondenceIncidenceTorCoefficient k p (projection p ≫ p) h
            (correspondenceGraphMap p (projection p ≫ p) (endpoint p c) (by simp) s.val) w t :=
  componentCorrespondence_graphEndpointTorCoefficient p h q j U hU F hF g hg z c s

#print axioms Stacks.Chow.PrincipalBoundary.componentCorrespondence_graphEndpointTorCoefficient

end Stacks.Chow.PrincipalBoundary
