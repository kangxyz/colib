/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.MotivicCohomology.FieldTopDegree

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.PresheafWithTransfers
open AlgebraicGeometry.PresheafWithTransfers.FieldTopDegree

universe w u
variable (k : Type u) [Field k]

-- These consume the actual sheafified complex, with no raw-complex comparison premise.
example (p : ℤ) (q : ℕ) (hp : (q : ℤ) < p) : IsZero ((motivicBaseComplex k q).X p) :=
  isZero_base_X k p q hp

example (p : ℤ) (q : ℕ) (hp : (q : ℤ) < p) :
    IsZero ((motivicBaseComplex k q).homology p) :=
  isZero_base_homology k p q hp

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

example (p : ℤ) (q : ℕ) (hp : (q : ℤ) < p) :
    Subsingleton (motivicCohomology k p q (SmoothSite.base (Spec (.of k)))) :=
  subsingleton_integral_above k p q hp

example (p : ℤ) (q n : ℕ) (hp : (q : ℤ) < p) :
    Subsingleton (motivicFiniteCohomology k p q n (SmoothSite.base (Spec (.of k)))) :=
  subsingleton_finite_above k p q n hp

example (q n : ℕ) :
    motivicFiniteCohomology k (q : ℤ) q n (SmoothSite.base (Spec (.of k))) ≃+
      integralModulo k q n :=
  topDegreeFiniteEquiv k q n

example (q n : ℕ)
    (x : motivicCohomology k (q : ℤ) q (SmoothSite.base (Spec (.of k)))) :
    topDegreeFiniteEquiv k q n (motivicBaseIntegralReduction k (q : ℤ) q n x) =
      (QuotientAddGroup.mk x : integralModulo k q n) :=
  topDegreeFiniteEquiv_integralReduction k q n x

example (q n : ℕ) :
    (motivicBaseIntegralReduction k (q : ℤ) q n).ker = integralMultiples k q n :=
  integralReduction_ker k q n

example (q : ℕ) :
    motivicFiniteCohomology k (q : ℤ) q 0 (SmoothSite.base (Spec (.of k))) ≃+
      integralModulo k q 0 :=
  topDegreeFiniteEquiv k q 0

example (q : ℕ) :
    motivicFiniteCohomology k (q : ℤ) q 1 (SmoothSite.base (Spec (.of k))) ≃+
      integralModulo k q 1 :=
  topDegreeFiniteEquiv k q 1
