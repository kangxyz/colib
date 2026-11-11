/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.IdealProduct
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.TensorZeroProduct

/-!
# Whole tensor-section spans and the original signed pole expression

Native tensor zero-ideal multiplication is converted into native span additivity
using actual regularity and whole finite-flat hypotheses. The signed identity
has the original order `(A - B) - (D - N)`, so the numerator N occurs positively.
It is an equality of whole support correspondences before any reduction.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Divisors

universe u

namespace AlgebraicGeometry.Cor

open Scheme Scheme.RelativeCurvePencil

variable {k : Type u} [Field k] {X Y : SmoothSite (Spec (.of k))} {C : Scheme.{u}}
  (m : C ⟶ pullback X.hom Y.hom) [IsFinite m]
  (M N : C.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property M]
  [AlgebraicGeometry.SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property N]
  (a : Γ(M, ⊤)) (n : Γ(N, ⊤))

local notation "A" => zeroScheme C M a
local notation "N₀" => zeroScheme C N n
local notation "T" => zeroScheme C (tensorModules M N) (tensorSection M N ⊤ a n)
local notation "p" => m ≫ pullback.fst X.hom Y.hom
local notation "g" => m ≫ pullback.snd X.hom Y.hom
local notation "span[" I "]" => ofFiniteFlatSpan ((I).subschemeι ≫ p)
  ((I).subschemeι ≫ g) (by simp only [Category.assoc, pullback.condition])

variable [IsFinite (A.subschemeι ≫ p)] [Flat (A.subschemeι ≫ p)]
  [IsFinite (N₀.subschemeι ≫ p)] [Flat (N₀.subschemeι ≫ p)]
  [IsFinite (T.subschemeι ≫ p)] [Flat (T.subschemeι ≫ p)]

/-- The whole native tensor-section span is the sum of the actual factors. -/
theorem ofFiniteFlatSpan_tensorSection
    (hn : IsEffectiveCartierDivisor N₀) : span[T] = span[A] + span[N₀] :=
  ofFiniteFlatSpan_add_of_ideal_product m A N₀ T
    (isLocallyPrincipal_zeroScheme C M a) hn (zeroScheme_tensorSection_eq_mul M N a n)

variable (b : Γ(M, ⊤)) (d : Γ(N, ⊤))

local notation "B" => zeroScheme C M b
local notation "D" => zeroScheme C N d
local notation "P" => zeroScheme C (tensorModules M N) (tensorSection M N ⊤ b d)

variable [IsFinite (B.subschemeι ≫ p)] [Flat (B.subschemeι ≫ p)]
  [IsFinite (D.subschemeι ≫ p)] [Flat (D.subschemeι ≫ p)]
  [IsFinite (P.subschemeι ≫ p)] [Flat (P.subschemeι ≫ p)]

/-- Subtracting the actual product pole gives precisely the original lambda/psi
signs, retaining the original whole zero-scheme correspondences. -/
theorem ofFiniteFlatSpan_tensorSection_sub_pole
    (hn : IsEffectiveCartierDivisor N₀) (hd : IsEffectiveCartierDivisor D) :
    span[T] - span[P] = (span[A] - span[B]) - (span[D] - span[N₀]) := by
  rw [ofFiniteFlatSpan_tensorSection m M N a n hn,
    ofFiniteFlatSpan_tensorSection m M N b d hd]
  abel

end AlgebraicGeometry.Cor
