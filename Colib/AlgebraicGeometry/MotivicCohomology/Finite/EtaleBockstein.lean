/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.EtaleDerivedComparison
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.DerivedBockstein

/-!
# Signed Bockstein compatibility in consecutive motivic degrees

The original finite and integral motivic groups are retained. The signed cone
boundary and its actual etale image are normalized to degrees p and p + 1.
No Tate identification, comparison isomorphism or ordinary Sheaf.H endpoint
is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.FreeYonedaUnivLE

universe w w' u

namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]
variable [HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1}]
variable [(Cor.nisnevichTopology k).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [(Cor.nisnevichTopology k).PreservesSheafification
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [HasSheafify (SmoothSite.nisnevichTopology (Spec (.of k)))
  AddCommGrpCat.{u + 1}]

variable [HasSheafify (SmoothSite.etaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1}]
variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{w'}
  (Sheaf (SmoothSite.etaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The signed coefficient-cone boundary on the original motivic groups in degrees `p`, `p + 1`. -/
def motivicCohomologyBockstein (p : ℤ) (q n : ℕ)
    (X : SmoothSite (Spec (.of k))) :
    motivicFiniteCohomology k p q n X →+ motivicCohomology k (p + 1) q X :=
  SmoothSite.derivedBocksteinDegree (Spec (.of k)) X (motivicSheafComplex k q) n p

/-- Integral etale hypercohomology of the actual sheafified motivic complex. -/
abbrev motivicEtaleCohomology (p : ℤ) (q : ℕ)
    (X : SmoothSite (Spec (.of k))) : Type w' :=
  ((DerivedCategory.singleFunctor _ 0).obj
    ((freeYoneda.{u + 1} (SmoothSite.etaleTopology (Spec (.of k)))).obj X) ⟶
      (DerivedCategory.Q.obj (motivicEtaleSheafComplex k q))⟦p⟧)

/-- The exact comparison on the original integral motivic group. -/
def motivicEtaleCohomologyComparison (p : ℤ) (q : ℕ)
    (X : SmoothSite (Spec (.of k))) :
    motivicCohomology k p q X →+ motivicEtaleCohomology k p q X :=
  SmoothSite.nisnevichToEtaleDerivedHomMap (Spec (.of k)) X (motivicSheafComplex k q) p

/-- The actual mapped signed coefficient boundary with target in degree `p + 1`. -/
def motivicEtaleCohomologyBockstein (p : ℤ) (q n : ℕ)
    (X : SmoothSite (Spec (.of k))) :
    motivicFiniteEtaleCohomology k p q n X →+ motivicEtaleCohomology k (p + 1) q X :=
  SmoothSite.etaleDerivedBocksteinDegree (Spec (.of k)) X (motivicSheafComplex k q) n p

omit [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})] in
/-- The etale operation is the original signed Bockstein on the actual target cone,
through the canonical finite-cone comparison, with its degree normalized to `p + 1`. -/
theorem motivicEtaleCohomologyBockstein_eq (p : ℤ) (q n : ℕ)
    (X : SmoothSite (Spec (.of k))) (a : motivicFiniteEtaleCohomology k p q n X) :
    motivicEtaleCohomologyBockstein k p q n X a =
      (a ≫ (DerivedCategory.Q.map (motivicFiniteEtaleSheafComplexIso k q n).hom)⟦p⟧') ≫
        CochainComplex.finiteCoefficients.derivedBockstein (motivicEtaleSheafComplex k q) n p := by
  change a ≫ CochainComplex.finiteCoefficients.mappedDerivedBockstein
    (SmoothSite.nisnevichToEtaleSheaf (Spec (.of k)) AddCommGrpCat.{u + 1})
    (motivicSheafComplex k q) n p = _
  rw [CochainComplex.finiteCoefficients.mappedDerivedBockstein_eq]
  exact (Category.assoc _ _ _).symm

/-- The actual finite and integral derived comparisons commute with the original signed
Bockstein after native degree normalization, in every integer cohomological degree. -/
@[colib_tag "COL-1228"]
theorem motivicFiniteEtaleCohomologyComparison_bockstein (p : ℤ) (q n : ℕ)
    (X : SmoothSite (Spec (.of k))) (a : motivicFiniteCohomology k p q n X) :
    motivicEtaleCohomologyComparison k (p + 1) q X
      (motivicCohomologyBockstein k p q n X a) =
    motivicEtaleCohomologyBockstein k p q n X
      (motivicFiniteEtaleCohomologyComparison k p q n X a) :=
  SmoothSite.nisnevichToEtaleDerivedHomMap_bockstein_degree
    (Spec (.of k)) X (motivicSheafComplex k q) n p a

end AlgebraicGeometry.PresheafWithTransfers
