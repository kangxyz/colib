/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Hypercohomology.Evaluation
public import Colib.AlgebraicGeometry.Sites.Smooth.Cohomology.FieldEvaluation

/-!
# Unbounded Nisnevich hypercohomology at the smooth base field

For any field `k`, the native free sheaf representing sections at the base
object of its smooth Nisnevich site is projective by the previously established
field-cover splitting theorem. Consequently, for every integer degree and every
unbounded coefficient complex, the existing hypercohomology group is the
cohomology of that complex evaluated termwise at `Spec k`.

This is an actual application of the generic evaluation theorem. It is restricted
to the base field on its own smooth site, not an arbitrary extension field or an
etale site. It constructs no motivic coefficient complex. The field-cover input
is Mazza--Voevodsky--Weibel, Lecture 12, Example 12.2, printed p. 89; that statement
supplies projectivity, not the unbounded derived comparison itself.

The original implementation is
`Motivic/Aglib/AlgebraicGeometry/Sites/Hypercohomology/FieldEvaluation.lean`
at motivic commit `a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.Cohomology.FreeYonedaUnivLE

universe w u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Unbounded hypercohomology at the actual base field is cohomology of its sections complex. -/
def hypercohomologyBaseFieldAddEquiv
    (K : CochainComplex (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) ℤ)
    (n : ℤ) :
    (hypercohomologyPresheaf.{w, u + 1} (nisnevichTopology (Spec (.of k))) K n).obj
      (op (base (Spec (.of k)))) ≃+
        ((((sheafSections (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).obj
          (op (base (Spec (.of k))))).mapHomologicalComplex (.up ℤ)).obj K).homology n := by
  letI := projective_freeYoneda_base k
  exact hypercohomologyEvaluationAddEquiv.{w, u + 1} _ _ K n

/-- The field comparison intertwines actual coefficient cochain maps in every integer degree. -/
theorem hypercohomologyBaseFieldAddEquiv_naturality
    {K L : CochainComplex (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) ℤ}
    (f : K ⟶ L) (n : ℤ)
    (x : (hypercohomologyPresheaf.{w, u + 1} (nisnevichTopology (Spec (.of k))) K n).obj
      (op (base (Spec (.of k))))) :
    hypercohomologyBaseFieldAddEquiv k L n
      (((hypercohomologyPresheafFunctor.{w, u + 1} (nisnevichTopology (Spec (.of k))) n).map f).app
        (op (base (Spec (.of k)))) x) =
      HomologicalComplex.homologyMap
        ((((sheafSections (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).obj
          (op (base (Spec (.of k))))).mapHomologicalComplex (.up ℤ)).map f) n
        (hypercohomologyBaseFieldAddEquiv k K n x) := by
  let := projective_freeYoneda_base k
  exact hypercohomologyEvaluationAddEquiv_naturality.{w, u + 1} _ _ f n x

end AlgebraicGeometry.Scheme.SmoothSite

attribute [colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Sites/Hypercohomology/FieldEvaluation.lean:45-53"
  "specialization"
  "Base field of its smooth Nisnevich site; all integer degrees, unbounded coefficients"]
  AlgebraicGeometry.Scheme.SmoothSite.hypercohomologyBaseFieldAddEquiv

attribute [colib_ref "MVW2006" "Lecture 12, Example 12.2, p. 89"
  "ingredient" "Field-cover splitting supplies projectivity; not the unbounded comparison theorem"]
  AlgebraicGeometry.Scheme.SmoothSite.hypercohomologyBaseFieldAddEquiv

attribute [colib_tag "COL-0343"]
  AlgebraicGeometry.Scheme.SmoothSite.hypercohomologyBaseFieldAddEquiv
  AlgebraicGeometry.Scheme.SmoothSite.hypercohomologyBaseFieldAddEquiv_naturality
