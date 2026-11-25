/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# A prescribed five-path reassociation

Intended upstream module: `Aglib.Topology.Path.SpanReassociation`.

For five composable paths in an arbitrary topological space, `spanReassociation`
is the literal three-stage associator word. It retains every concatenation half cut
and reverses only the last associator's comparison coordinate.

Current consumers: the coefficient Bass span-composition carrier and its native
prespectrum evaluation adapter `SpanReassociationEvaluation`.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Topology unitInterval
universe v
namespace Path.Homotopy
variable {X : Type v} [TopologicalSpace X] {a b c d e f : X}

/-- The exact three-stage reassociation used by the original identical-leg span composition. -/
def spanReassociation (P : Path a b) (Q : Path b c) (T : Path c d)
    (U : Path d e) (V : Path e f) :
    (P.trans ((Q.trans (T.trans U)).trans V)).Homotopy
      ((P.trans Q).trans (T.trans (U.trans V))) :=
  ((refl P).hcomp (transAssoc Q (T.trans U) V)).trans
    (((refl P).hcomp ((refl Q).hcomp (transAssoc T U V))).trans
      (transAssoc P Q (T.trans (U.trans V))).symm)

end Path.Homotopy
