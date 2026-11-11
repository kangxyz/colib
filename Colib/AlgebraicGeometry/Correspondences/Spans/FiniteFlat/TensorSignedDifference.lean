/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.TensorProduct

/-!
# Signed tensor products with different factor line modules

The actual normalized pencil has `a` in the graph line tensored with the pole
line, whereas `b` is in the pole line. They are not sections of the same module.
This theorem allows all four factor modules to differ and therefore preserves
that original scope. Only actual tensor zero schemes and whole finite-flat spans
occur; no comparison of their line modules is required for cycle subtraction.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Divisors

universe u

namespace AlgebraicGeometry.Cor

open Scheme

variable {k : Type u} [Field k] {X Y : SmoothSite (Spec (.of k))} {C : Scheme.{u}}
  (m : C ⟶ pullback X.hom Y.hom) [IsFinite m]
  (MA MB MN MD : C.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property MA]
  [AlgebraicGeometry.SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property MB]
  [AlgebraicGeometry.SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property MN]
  [AlgebraicGeometry.SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property MD]
  (a : Γ(MA, ⊤)) (b : Γ(MB, ⊤)) (n : Γ(MN, ⊤)) (d : Γ(MD, ⊤))

local notation "A" => zeroScheme C MA a
local notation "B" => zeroScheme C MB b
local notation "N" => zeroScheme C MN n
local notation "D" => zeroScheme C MD d
local notation "T" => zeroScheme C (tensorModules MA MN) (tensorSection MA MN ⊤ a n)
local notation "P" => zeroScheme C (tensorModules MB MD) (tensorSection MB MD ⊤ b d)
local notation "p" => m ≫ pullback.fst X.hom Y.hom
local notation "g" => m ≫ pullback.snd X.hom Y.hom
local notation "span[" I "]" => ofFiniteFlatSpan ((I).subschemeι ≫ p)
  ((I).subschemeι ≫ g) (by simp only [Category.assoc, pullback.condition])

variable [IsFinite (A.subschemeι ≫ p)] [Flat (A.subschemeι ≫ p)]
  [IsFinite (B.subschemeι ≫ p)] [Flat (B.subschemeι ≫ p)]
  [IsFinite (N.subschemeι ≫ p)] [Flat (N.subschemeι ≫ p)]
  [IsFinite (D.subschemeι ≫ p)] [Flat (D.subschemeι ≫ p)]
  [IsFinite (T.subschemeι ≫ p)] [Flat (T.subschemeι ≫ p)]
  [IsFinite (P.subschemeι ≫ p)] [Flat (P.subschemeι ≫ p)]

/-- The original signed pole cancellation, without identifying unrelated line modules. -/
theorem ofFiniteFlatSpan_tensorProducts_sub
    (hn : IsEffectiveCartierDivisor N) (hd : IsEffectiveCartierDivisor D) :
    span[T] - span[P] = (span[A] - span[B]) - (span[D] - span[N]) := by
  rw [ofFiniteFlatSpan_tensorSection m MA MN a n hn,
    ofFiniteFlatSpan_tensorSection m MB MD b d hd]
  abel

end AlgebraicGeometry.Cor
