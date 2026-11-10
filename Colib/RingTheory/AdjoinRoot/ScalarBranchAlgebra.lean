/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdjoinRoot.FactorIndexEquiv

/-!
# Literal old-root actions on the native scalar factors

The two lower algebraic constructions used by the complete-DVR scalar-branch
consumer are adapted from `Aglib/RingTheory/AdjoinRootNestedBaseChange.lean`
at revision `4f65be4eafa8964bd1f7a83682e99aa8165bd418`, lines 35–47.
The full nested tensor decomposition is already supplied by native factor
modules and is not rebuilt here. These are the original quotient map and its
base scalar tower, on the existing native factor subtype.
-/

@[expose] public noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

namespace AdjoinRoot

variable {k L : Type*} [Field k] [Field L] [Algebra k L]
  (p : k[X])
  (r : {r : Σ e : ℕ, MonicIrreducibleOfDegree L e //
    poly r.2 ∣ p.map (algebraMap k L)})

/-- The old-root action on each native scalar factor is its literal quotient map. -/
@[instance_reducible]
def scalarBranchAlgebra : Algebra (AdjoinRoot p) (AdjoinRoot (poly r.1.2)) :=
  (AdjoinRoot.map (algebraMap k L) p (poly r.1.2) r.2).toAlgebra

attribute [local instance] scalarBranchAlgebra

/-- The actual quotient map preserves the original coefficient-field tower. -/
theorem scalarBranchBaseTower : IsScalarTower k (AdjoinRoot p) (AdjoinRoot (poly r.1.2)) :=
  IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro a
    exact (AdjoinRoot.map_of (algebraMap k L) p (poly r.1.2) r.2 a).symm)

end AdjoinRoot

end
