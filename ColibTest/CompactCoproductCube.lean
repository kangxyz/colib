/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Additivity.CompactCoproductCube

/-! # Exact compact coproduct lifts, entire faces and original degree-zero cubes -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory.Waldhausen.Product SSet
open CategoryTheory CategoryTheory.Limits Topology CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.Additivity
open scoped Topology
universe u v
namespace ColibTest.CompactCoproductCube
variable {C : Type u} [Category.{v} C] (W : Structure C) (n : ℕ)

/-- The exact original product projections are retained. -/
theorem original_projections
    (p q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint)
    (z : Fin (n + 1) → unitInterval) :
    Product.deloopingComparison W W (productCubeLift W n p q z) = (p z, q z) :=
  productCubeLift_projection W n p q z

/-- A prescribed whole face is recovered without any compactness premise on its index. -/
theorem original_entire_face {S : Type}
    (p q : C(unitInterval × unitInterval,
      GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint)) (i : S → unitInterval × unitInterval)
    (g : S → GenLoop (Fin (n + 1)) (productStructure W W).Delooping
      (productStructure W W).kBasepoint)
    (hg : ∀ s z, Product.deloopingComparison W W (g s z) = (p (i s) z, q (i s) z))
    (s : S) : productCubeFamily W n p q (i s) = g s :=
  productCubeFamily_face W n p q i g hg s

variable [HasBinaryCoproducts C]

/-- Independent null and deformation times remain inside the single compact family. -/
theorem independent_times_boundary
    (p q : C(unitInterval × unitInterval,
      GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint)) (s t : unitInterval)
    (z : Fin (n + 1) → unitInterval) (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    coproductCubeFamily W n p q (s, t) z = W.kBasepoint :=
  coproductCubeFamily_boundary W n p q (s, t) z hz

/-- The original one-coordinate cube is retained in degree zero. -/
theorem original_degree_zero (p q : GenLoop (Fin (0 + 1)) W.Delooping W.kBasepoint)
    (z : Fin (0 + 1) → unitInterval) :
    coproductCube W 0 p q z = coproductBasedMap W (productCubeLift W 0 p q z) :=
  coproductCube_apply W 0 p q z

/-- A supplied entire null path remains the actual input to the compact lift. -/
theorem original_null_path
    {p : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint}
    (N : Path p GenLoop.const) (q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint)
    (t : unitInterval) :
    coproductCubePath W n N (Path.refl q) t = coproductCube W n (N t) q :=
  coproductCubePath_apply W n N (Path.refl q) t

end ColibTest.CompactCoproductCube
