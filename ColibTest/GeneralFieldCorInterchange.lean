/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Monoidal.Interchange

/-!
# General-field correspondence interchange regression

The signature test deliberately provides only a field, not a perfect-field instance.
The axiom reports audit the native weighted route and the final interchange theorem.
-/

noncomputable section

universe u

example {k : Type u} [Field k] : AlgebraicGeometry.Cor.ExteriorInterchange k :=
  AlgebraicGeometry.Cor.exteriorInterchange

#print axioms Stacks.Chow.exteriorPointCycle_apply_generic
#print axioms Stacks.Chow.exteriorPointCycle_apply_closedProduct
#print axioms Stacks.Chow.structureTorCoefficient_wholeIncidence_weighted
#print axioms Stacks.Chow.structureTorCoefficient_wholeIncidence_native
#print axioms Stacks.Chow.exteriorWholeIncidenceTorCycle_eq_weighted_sum
#print axioms Stacks.Chow.incidenceTorPairing_exteriorPrimes
#print axioms AlgebraicGeometry.Cor.exteriorInterchange

#check @AlgebraicGeometry.Cor.exteriorInterchange
