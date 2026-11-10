/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.FieldTheory.AdjoinRoot.SeparablePresentation
import Mathlib.FieldTheory.Galois.Basic

open Polynomial

universe u v

example {K : Type u} [Field K] (p : K[X]) [Fact (Irreducible p)]
    (hp : p.Monic) [Algebra.IsSeparable K (AdjoinRoot p)] : p.Separable :=
  AdjoinRoot.polynomial_separable_of_isSeparable p hp

-- The Galois ambient has an independent universe, and the map is the actual embedding.
example {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (p : K[X]) [Fact (Irreducible p)] (hp : p.Monic)
    (f : AdjoinRoot p →ₐ[K] L) : p.Separable :=
  AdjoinRoot.polynomial_separable_of_algHom p hp f

-- Any supplied presentation of the original separable field gives the same polynomial fact.
example {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Algebra.IsSeparable K L] (p : K[X]) [Fact (Irreducible p)] (hp : p.Monic)
    (f : L ≃ₐ[K] AdjoinRoot p) : p.Separable :=
  AdjoinRoot.polynomial_separable_of_algHom p hp f.symm.toAlgHom
