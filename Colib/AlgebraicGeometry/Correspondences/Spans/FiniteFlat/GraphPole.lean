/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.TensorProduct
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Sum
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierComplement

/-!
# Cancellation of the genuine graph-times-pole tensor section

The entire graph-canonical-section times two pole sections has zero ideal
`graph * (pole₁ * pole₂)`. The pole is actually Cartier. Actual whole finite-flat
span additivity then cancels the same whole pole, not just its reduced support.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Divisors

universe u

namespace AlgebraicGeometry.Cor

open Scheme Scheme.RelativeCurvePencil

variable {k : Type u} [Field k] {X Y : SmoothSite (Spec (.of k))} {C : Scheme.{u}}
  (m : C ⟶ pullback X.hom Y.hom) [IsFinite m]
  (G : C.IdealSheafData) [IsEffectiveCartierDivisor G]
  (M N : C.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property M]
  [AlgebraicGeometry.SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property N]
  (b : Γ(M, ⊤)) (d : Γ(N, ⊤))

local notation "B" => zeroScheme C M b
local notation "D" => zeroScheme C N d
local notation "P" => zeroScheme C (tensorModules M N) (tensorSection M N ⊤ b d)
local notation "T" => zeroScheme C (tensorModules (tensorModules (divisorSheaf G) M) N)
  (tensorSection (tensorModules (divisorSheaf G) M) N ⊤
    (tensorSection (divisorSheaf G) M ⊤ (divisorSheafGlobalSection G) b) d)
local notation "p" => m ≫ pullback.fst X.hom Y.hom
local notation "g" => m ≫ pullback.snd X.hom Y.hom
local notation "span[" I "]" => ofFiniteFlatSpan ((I).subschemeι ≫ p)
  ((I).subschemeι ≫ g) (by simp only [Category.assoc, pullback.condition])

variable [IsFinite (G.subschemeι ≫ p)] [Flat (G.subschemeι ≫ p)]
  [IsFinite (P.subschemeι ≫ p)] [Flat (P.subschemeι ≫ p)]
  [IsFinite (T.subschemeι ≫ p)] [Flat (T.subschemeι ≫ p)]

/-- Subtracting the actual full product pole leaves precisely the full graph-divisor span. -/
theorem ofFiniteFlatSpan_graph_tensor_poles_sub
    (hb : IsEffectiveCartierDivisor B) (hd : IsEffectiveCartierDivisor D) :
    span[T] - span[P] = span[G] := by
  have hp : IsEffectiveCartierDivisor P := by
    rw [zeroScheme_tensorSection_eq_mul]
    exact isEffectiveCartierDivisor_mul B D hb hd
  have ht : T = G * P := by
    rw [zeroScheme_graph_tensor_poles, zeroScheme_tensorSection_eq_mul, mul_assoc]
  have hsum := ofFiniteFlatSpan_add_of_ideal_product m G P T
    (isLocallyPrincipal_of_isEffectiveCartierDivisor G inferInstance) hp ht
  rw [hsum]
  abel

end AlgebraicGeometry.Cor
