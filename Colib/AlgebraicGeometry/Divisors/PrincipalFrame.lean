/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionZeroScheme
public import StacksFrontier.AlgebraicGeometry.InvertibleDual.SectionIdeal
public import StacksFrontier.AlgebraicGeometry.NonvanishingTrivialization.Basic

/-!
# The divisor frame of a specified regular principal ideal

Evaluation on the specified generator of the ideal gives the dual divisor frame.
The canonical section has coordinate equal to that generator, not to one. This
applies on the entire affine scheme, even where the generator vanishes.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.SheafOfModules (DualBasisOne dualEval)

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} (D : X.IdealSheafData)

/-- Evaluation on a global basis of the actual ideal sheaf. -/
def divisorBasisFrameHom
    (b : DualBasisOne X.presheaf (structureSheafRing X.toRingedSpace).property
      (negativeTwist' D) (⊤ : X.Opens)) :
    divisorSheaf D ⟶ SheafOfModules.unit X.ringCatSheaf :=
  Scheme.Modules.evalGlobalHom (negativeTwist' D) b.e

/-- Evaluation on an ideal basis is an isomorphism on every open. -/
instance isIso_divisorBasisFrameHom
    (b : DualBasisOne X.presheaf (structureSheafRing X.toRingedSpace).property
      (negativeTwist' D) (⊤ : X.Opens)) : IsIso (divisorBasisFrameHom D b) := by
  apply Stacks.SheafOfModules.isIso_of_isIso_val_app
  intro U
  rw [ConcreteCategory.isIso_iff_bijective]
  let bU := b.restrict (homOfLE (le_top : U.unop ≤ ⊤))
  change Function.Bijective (fun μ => dualEval μ bU.e)
  refine ⟨fun μ ν h => dualEval_injective_of_dualBasisOne D bU h, ?_⟩
  intro c
  refine ⟨c • bU.lam, ?_⟩
  change dualEval (c • bU.lam) bU.e = c
  rw [dualEval, Stacks.SheafOfModules.evalSection_smul_left]
  change c * dualEval bU.lam bU.e = c
  rw [bU.eval_self]
  exact mul_one c

/-- The dual frame determined by a global basis of the actual ideal. -/
def divisorBasisFrame
    (b : DualBasisOne X.presheaf (structureSheafRing X.toRingedSpace).property
      (negativeTwist' D) (⊤ : X.Opens)) :
    divisorSheaf D ≅ SheafOfModules.unit X.ringCatSheaf :=
  asIso (divisorBasisFrameHom D b)

/-- The frame sends the canonical section to the literal underlying ideal generator. -/
theorem divisorBasisFrame_canonicalSection
    (b : DualBasisOne X.presheaf (structureSheafRing X.toRingedSpace).property
      (negativeTwist' D) (⊤ : X.Opens)) :
    (divisorBasisFrame D b).hom.app ⊤ (divisorSheafGlobalSection D) =
      idealSheafSection D b.e := by
  change idealSheafSection D
    ((Scheme.Modules.presheaf (negativeTwist' D)).map
      (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op b.e) = _
  simp

variable [IsAffine X] {f : Γ(X, ⊤)}
  (hf : D.ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {f})
  (hreg : f ∈ nonZeroDivisors Γ(X, ⊤))

/-- The frame of `𝒪(D)` constructed from its given regular principal equation. -/
def principalDivisorFrame : divisorSheaf D ≅ SheafOfModules.unit X.ringCatSheaf :=
  divisorBasisFrame D (dualBasisOneOfPrincipal D ⟨⊤, isAffineOpen_top X⟩ hf hreg)

/-- The prescribed equation, rather than an unspecified unit multiple, is the coordinate. -/
theorem principalDivisorFrame_canonicalSection :
    (principalDivisorFrame D hf hreg).hom.app ⊤ (divisorSheafGlobalSection D) = f := by
  refine (divisorBasisFrame_canonicalSection D
    (dualBasisOneOfPrincipal D ⟨⊤, isAffineOpen_top X⟩ hf hreg)).trans ?_
  have h : ∃ y, idealSheafSection D y = f :=
    (mem_ideal_iff_exists_idealSheafSection D ⟨⊤, isAffineOpen_top X⟩ f).1
      (hf ▸ Ideal.mem_span_singleton_self f)
  exact h.choose_spec

end Stacks.Divisors
