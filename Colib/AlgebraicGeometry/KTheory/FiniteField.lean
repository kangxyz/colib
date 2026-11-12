/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.CoherentAffineComparison
public import Colib.RingTheory.KTheory.Quillen.Field.FiniteFieldGTwo

/-!
# Coherent G₂ of the spectrum of a finite field

The actual affine global-sections comparison identifies the unchanged public
coherent G₂ group with the already proved trivial finite-module group.

Implementation source: `Quillen/KTheory/Field/FiniteFieldKTwo.lean`,
`specGTwo_subsingleton` and `specGTwo_eq_one`, at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
universe u
open AlgebraicGeometry
namespace Quillen.Field
variable (F : Type u) [Field F] [Finite F]

/-- The actual public coherent G₂ group of the spectrum of a finite field is trivial. -/
theorem specGTwo_subsingleton : Subsingleton (Scheme.G (Spec (CommRingCat.of F)) 2) := by
  constructor
  intro a b
  apply (Scheme.Modules.Coherent.publicSpecGRingEquiv (CommRingCat.of F) 2).injective
  exact @Subsingleton.elim _ (finiteModuleGTwo_subsingleton F) _ _

/-- Every class in the original public coherent G₂ group of a finite field is neutral. -/
theorem specGTwo_eq_one (a : Scheme.G (Spec (CommRingCat.of F)) 2) : a = 1 :=
  @Subsingleton.elim _ (specGTwo_subsingleton F) a 1

end Quillen.Field

attribute [colib_tag "COL-0614",
  colib_ref "quillen" "Quillen/KTheory/Field/FiniteFieldKTwo.lean, specGTwo clauses"
    "adaptation" "The actual public coherent G2 group via affine global sections"]
  Quillen.Field.specGTwo_subsingleton Quillen.Field.specGTwo_eq_one
