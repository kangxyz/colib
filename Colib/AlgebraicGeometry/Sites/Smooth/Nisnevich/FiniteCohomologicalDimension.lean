/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.CohomologicalDimension
import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.FiniteSimpleRefinement
import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.FiniteSplittingSequence
import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.ReducingSquares
import Colib.Util.References

/-!
# The smooth Nisnevich cohomological dimension bound

The geometric Nisnevich squares on a noetherian smooth site give complete
reducing refinements. Therefore the native free Nisnevich sheaf representing
a smooth object has projective dimension bounded by its topological Krull
dimension.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Stacks.Cohomology.FreeYonedaUnivLE

universe u w

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} [IsNoetherian S]

/-- Every smooth Nisnevich covering sieve over a noetherian base has a
simple refinement by geometric distinguished squares. -/
@[colib_tag "COL-1032", colib_ref "Voevodsky2008NisnevichCD" "§2, Proposition 2.16"
  "adaptation" "Simple refinements on the actual smooth separated finite-type site"]
theorem nisnevichSimpleRefinements_geometric :
    NisnevichSimpleRefinements (S := S) IsGeometricNisnevichSquare :=
  nisnevichSimpleRefinements_of_splittingSequences (by
    intro X Y q hq
    exact nisnevichSplittingSequence_of_singleton_mem_precoverage q hq)

/-- Ordinary Nisnevich cohomology vanishes above the topological Krull dimension. -/
@[colib_tag "COL-1032", colib_ref "Voevodsky2008CDTopologies" "§2, Theorem 2.26"
  "adaptation" "The dimension bound on the actual smooth Nisnevich site"]
theorem nisnevichCohomology_eq_zero_of_krullDim_lt
    [HasExt.{w} (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1})]
    (F : Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}) (n : ℕ) (X : SmoothSite S)
    (hd : topologicalKrullDim X.left < n)
    (x : (cohomologyPresheaf.{w, u + 1} F n).obj (op X)) : x = 0 :=
  nisnevichCohomology_eq_zero_of_topologicalKrullDim_lt (P := IsGeometricNisnevichSquare)
    (fun _ h ↦ h) nisnevichSimpleRefinements_geometric geometricNisnevichSquares_reduce F n X hd x

/-- The actual smooth Nisnevich free representing sheaf has projective
dimension at most any natural-number bound on the underlying Krull dimension. -/
@[colib_tag "COL-1032"]
theorem freeYoneda_hasProjectiveDimensionLE_of_krullDim_le
    (X : SmoothSite S) (d : ℕ) (hd : topologicalKrullDim X.left ≤ d) :
    HasProjectiveDimensionLE ((freeYoneda.{u + 1} (nisnevichTopology S)).obj X) d :=
  freeYoneda_hasProjectiveDimensionLE_of_topologicalKrullDim_le
    (P := IsGeometricNisnevichSquare) (fun _ h ↦ h) nisnevichSimpleRefinements_geometric
    geometricNisnevichSquares_reduce X d hd

end AlgebraicGeometry.Scheme.SmoothSite
