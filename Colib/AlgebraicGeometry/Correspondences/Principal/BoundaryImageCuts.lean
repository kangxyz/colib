/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Principal.BoundaryFamily
public import Colib.AlgebraicGeometry.Correspondences.Principal.ComponentCutPushforward

/-!
# Original boundary-principal coefficients under finite image cuts

The original integral support, source-target map, signed order, and native
finite-correspondence coefficient are unchanged. The full cut on its actual
integral image is compared with all source cuts using actual residue degrees.
Identifying the cut section with the endpoint incidence ideal is a later step.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Function.locallyFinsuppWithin

universe u

namespace Stacks.Chow.PrincipalBoundary

variable {C X Y S V : Scheme.{u}} [IsIntegral C] [IsNoetherian C]
  (p : X ⟶ S) (t : Y ⟶ S) [IsSeparated t] [LocallyOfFiniteType t]
  [IsAffine X] [V.IsQuasiAffine] (q : C ⟶ X) [IsProper q]
  (j : V ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
  (U : C.Opens) [Nonempty U] (hU : (Set.range j)ᶜ ⊆ (U : Set C))
  (f : Γ(C, U)) (hf : IsUnit f)
  (g : V ⟶ Y) (hg : j ≫ q ≫ p = g ≫ t)

/-- The original signed principal coefficient times all finite-fibre cuts equals
the actual native component-correspondence coefficient times the full image cut.
No support flatness, chosen fibre point, or rational-equivalence quotient occurs. -/
@[colib_tag "COL-1065", colib_ref "axiom_stacks_5ed82d14"
  "StacksFrontier/AlgebraicGeometry/Chow/PrincipalDivisorPushforward.lean:106-114"
  "ingredient" "Finite pushforward of original orders with full residue degrees; the cut- \
    length specialization is proved here."]
theorem componentCorrespondence_cutCoefficient
    [IsLocallyNoetherian (pullback p t)] (z : support U f) :
    let D := (integralComponentAt z.val).subscheme
    letI := isIntegral_integralComponentAt z.val
    let r := componentMap p t q j U hU f hf g hg z
    let e := integralImageMap r
    let E := (integralComponentAt (imagePoint p t q j U hU f hf g hg z)).subscheme
    ∀ (s : Γ(E, ⊤)),
      s ≠ 0 → ∀ y, Order.coheight y = 1 →
        (cycle U f) z.val *
          (∑ᶠ x ∈ e.base ⁻¹' {y},
            ((Module.length (D.presheaf.stalk x)
              (D.presheaf.stalk x ⧸ Ideal.span
                {D.presheaf.germ ⊤ x (by trivial) (e.appTop s)})).toNat : ℤ) *
                  (r.residueDegree x : ℤ)) =
        (componentCorrespondence p t q j U hU f hf g hg z).val
            (imagePoint p t q j U hU f hf g hg z) *
          ((Module.length (E.presheaf.stalk y)
            (E.presheaf.stalk y ⧸ Ideal.span
              {E.presheaf.germ ⊤ y (by trivial) s})).toNat : ℤ) := by
  classical
  let := isIntegral_integralComponentAt z.val
  let : IsLocallyNoetherian (integralComponentAt z.val).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (integralComponentAt z.val).subschemeι
  dsimp only
  intro s hs y hy
  have H := integralImageMap_principalCutLength
    (componentMap p t q j U hU f hf g hg z) s hs y hy
  rw [H]
  simp only [componentCorrespondence, single_apply]
  exact (mul_assoc _ _ _).symm

end Stacks.Chow.PrincipalBoundary
