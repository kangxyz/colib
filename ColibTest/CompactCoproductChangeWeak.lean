/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Additivity.CompactCoproductChangeWeak

/-! # Actual compact coproduct cubes under the original change-weak map -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory.Waldhausen.Product SSet
open CategoryTheory CategoryTheory.Limits Topology CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.Additivity CategoryTheory.Waldhausen.Fibration
open scoped Topology
universe u v
namespace ColibTest.CompactCoproductChangeWeak
variable {C : Type u} [Category.{v} C] (W : Structure C)
  (N : NestedWeakEquivalences W) (n : ℕ)

/-- Both old product projections retain the actual change-weak maps. -/
theorem original_projections (x : (Product.productStructure W W).Delooping) :
    Product.deloopingComparison N.coarse N.coarse
      (changeWeakMap (Product.nestedWeakEquivalences W N) x) =
        (changeWeakMap N (Product.deloopingComparison W W x).1,
          changeWeakMap N (Product.deloopingComparison W W x).2) :=
  coproductProductComparison_changeWeak W N x

/-- Projection injectivity retains the complete original product lift. -/
theorem original_lift
    (p q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) :
    GenLoop.postcomp (changeWeakMap (Product.nestedWeakEquivalences W N))
      (changeWeakMap_basepoint (Product.nestedWeakEquivalences W N)) (productCubeLift W n p q) =
        productCubeLift N.coarse n (coproductChangeWeakCubeMap W N n p)
          (coproductChangeWeakCubeMap W N n q) :=
  productCubeLift_changeWeak W N n p q

variable [HasBinaryCoproducts C]

/-- The normalized compact coproduct commutes on the unchanged original cubes. -/
theorem original_coproduct
    (p q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) :
    coproductChangeWeakCubeMap W N n (coproductCube W n p q) =
      coproductCube N.coarse n (coproductChangeWeakCubeMap W N n p)
        (coproductChangeWeakCubeMap W N n q) :=
  coproductCube_changeWeak W N n p q

/-- Degree zero keeps the same one-coordinate input and original canonical normalization. -/
theorem original_degree_zero
    (p q : GenLoop (Fin (0 + 1)) W.Delooping W.kBasepoint) :
    coproductChangeWeakCubeMap W N 0 (coproductCube W 0 p q) =
      coproductCube N.coarse 0 (coproductChangeWeakCubeMap W N 0 p)
        (coproductChangeWeakCubeMap W N 0 q) :=
  coproductCube_changeWeak W N 0 p q

end ColibTest.CompactCoproductChangeWeak
