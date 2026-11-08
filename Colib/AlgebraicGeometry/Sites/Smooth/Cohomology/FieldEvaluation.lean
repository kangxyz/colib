/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Evaluation
public import Colib.CategoryTheory.Sites.Hypercohomology.Basic
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives

/-!
# Ordinary Nisnevich cohomology at the actual base field

The existing Stacks free representing sheaf at the smooth base object is
projective. Its positive ordinary Ext cohomology therefore vanishes for every
ordinary abelian coefficient sheaf. The field is arbitrary; the coefficient
universe remains `u + 1` and the Ext universe is independent.

This evaluates at `Spec k` on its own smooth site, not at an arbitrary extension
field, an affine-line cylinder, or a henselian stalk. No new cohomology object
is defined: the target is Stacks' original `cohomologyPresheaf`.

Adapted from `Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/Cohomology/FieldEvaluation.lean`
at `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`.
The geometric input is the field-cover splitting of Mazza--Voevodsky--Weibel,
Lecture 12, Example 12.2, printed p. 89; the cohomology convention is Definition
12.11 and Lemma 12.12, printed p. 92. Ext vanishing for projective sources is
reused directly from Mathlib.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.FreeYonedaUnivLE

universe w u

namespace AlgebraicGeometry.Scheme.SmoothSite

/-- The native free representing sheaf at the actual smooth base field is projective. -/
@[colib_tag "COL-0305"]
theorem projective_freeYoneda_base (k : Type u) [Field k] :
    Projective ((freeYoneda.{u + 1} (nisnevichTopology (Spec (.of k)))).obj
      (base (Spec (.of k)))) :=
  projective_freeYoneda _ _ (fun φ ↦ surjective_app_base_of_epi k φ)

variable (k : Type u) [Field k]
  [HasExt.{w} (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  (F : Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})

/-- Every positive-degree ordinary cohomology class at the actual base field vanishes. -/
@[colib_tag "COL-0305"]
theorem cohomologyPresheaf_succ_base_eq_zero (n : ℕ)
    (x : (cohomologyPresheaf.{w, u + 1} F (n + 1)).obj
      (op (base (Spec (.of k))))) : x = 0 := by
  let := projective_freeYoneda_base k
  change Ext.{w} ((freeYoneda.{u + 1} (nisnevichTopology (Spec (.of k)))).obj
    (base (Spec (.of k)))) F (n + 1) at x
  exact Ext.eq_zero_of_projective x

/-- The native positive-degree ordinary cohomology group at the base field is trivial. -/
@[colib_tag "COL-0305"]
theorem subsingleton_cohomologyPresheaf_succ_base (n : ℕ) :
    Subsingleton ((cohomologyPresheaf.{w, u + 1} F (n + 1)).obj
      (op (base (Spec (.of k))))) :=
  subsingleton_of_forall_eq 0 (cohomologyPresheaf_succ_base_eq_zero k F n)

/-- Positive-degree ordinary cohomology at the actual base field is a zero group object. -/
@[colib_tag "COL-0305"]
theorem isZero_cohomologyPresheaf_succ_base (n : ℕ) :
    IsZero ((cohomologyPresheaf.{w, u + 1} F (n + 1)).obj
      (op (base (Spec (.of k))))) := by
  let := subsingleton_cohomologyPresheaf_succ_base k F n
  exact AddCommGrpCat.isZero_of_subsingleton _

end AlgebraicGeometry.Scheme.SmoothSite

attribute [colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/Cohomology/FieldEvaluation.lean"
  "adaptation"
  "Projectivity and positive ordinary Ext vanishing at the base field, independent Ext universe"]
  AlgebraicGeometry.Scheme.SmoothSite.projective_freeYoneda_base
  AlgebraicGeometry.Scheme.SmoothSite.cohomologyPresheaf_succ_base_eq_zero
  AlgebraicGeometry.Scheme.SmoothSite.subsingleton_cohomologyPresheaf_succ_base
  AlgebraicGeometry.Scheme.SmoothSite.isZero_cohomologyPresheaf_succ_base

attribute [colib_ref "MVW2006"
  "Lecture 12, Example 12.2, p. 89; Definition 12.11 and Lemma 12.12, p. 92"
  "ingredient" "Split field covers and the ordinary Ext cohomology convention"]
  AlgebraicGeometry.Scheme.SmoothSite.cohomologyPresheaf_succ_base_eq_zero
