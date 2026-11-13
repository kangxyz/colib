/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.MilnorEquivalence
import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.CorestrictionFinite

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Chow
open AlgebraicGeometry.PresheafWithTransfers
open AlgebraicGeometry.MotivicCohomology
open DiagonalCorestriction DiagonalMilnorBoundaryDescent DiagonalMilnorEquivalence
open DiagonalMilnorSymbol DiagonalSymbolFieldChange

universe w u

variable {k L : Type u} [Field k] [Field L]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of L))) AddCommGrpCat.{u + 1})]

example [Algebra k L] [FiniteDimensional k L] (q n : ℕ)
    (x : motivicCohomology L q q (SmoothSite.base (Spec (.of L)))) :
    finiteCorestriction (k := k) (E := L) q n (motivicBaseIntegralReduction L q q n x) =
      motivicBaseIntegralReduction k q q n (integralCorestriction (k := k) (E := L) q x) :=
  finiteCorestriction_integralReduction q n x

example (q : ℕ) (x : motivicCohomology k q q (SmoothSite.base (Spec (.of k)))) :
    motivicSymbol k q (motivicNorm k q x) = x :=
  motivicSymbol_motivicNorm k q x

example (q : ℕ) (x : MilnorKTheory k q) :
    motivicNorm k q (motivicSymbol k q x) = x :=
  motivicNorm_motivicSymbol k q x

example (φ : k →+* L) (q : ℕ) (x : MilnorKTheory k q) :
    motivicFieldChange φ q (motivicEquiv k q x) =
      motivicEquiv L q (milnorKTheoryMap φ q x) :=
  motivicSymbol_fieldChange φ q x

example (φ : k →+* L) (q : ℕ)
    (x : motivicCohomology k q q (SmoothSite.base (Spec (.of k)))) :
    motivicNorm L q (motivicFieldChange φ q x) = milnorKTheoryMap φ q (motivicNorm k q x) :=
  motivicNorm_fieldChange q φ x

example [Algebra k L] [FiniteDimensional k L] (q : ℕ) (x : MilnorKTheory L q) :
    motivicEquiv k q (milnorKNorm k L q x) =
      integralCorestriction (k := k) (E := L) q (motivicEquiv L q x) :=
  motivicSymbol_finiteExtensionNorm q x

example [Algebra k L] [FiniteDimensional k L] (q : ℕ)
    (x : motivicCohomology L q q (SmoothSite.base (Spec (.of L)))) :
    motivicNorm k q (integralCorestriction (k := k) (E := L) q x) =
      milnorKNorm k L q (motivicNorm L q x) :=
  motivicNorm_corestriction q x

end
