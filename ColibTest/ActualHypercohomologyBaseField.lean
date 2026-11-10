/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Sites.Smooth.Hypercohomology.FieldEvaluation

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme.SmoothSite
open Stacks.Cohomology.FreeYonedaUnivLE

universe w u

section

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  (K : CochainComplex (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) ℤ)

example (n : ℤ) : Function.Bijective (hypercohomologyBaseFieldAddEquiv k K n) :=
  (hypercohomologyBaseFieldAddEquiv k K n).bijective

example (n : ℤ) (x : (hypercohomologyPresheaf.{w, u + 1} (nisnevichTopology (Spec (.of k))) K n).obj
    (op (base (Spec (.of k))))) :
    (hypercohomologyBaseFieldAddEquiv k K n).symm
      (hypercohomologyBaseFieldAddEquiv k K n x) = x :=
  AddEquiv.symm_apply_apply _ x

end

#print axioms AlgebraicGeometry.Scheme.SmoothSite.hypercohomologyBaseFieldAddEquiv
#print axioms AlgebraicGeometry.Scheme.SmoothSite.hypercohomologyBaseFieldAddEquiv_naturality
