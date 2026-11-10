/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.Graph

/-!
# In-package checks for native exterior Graphs
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme Stacks.Chow
universe u
variable {k : Type u} [Field k] (X Y T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]

example (φ : X ⟶ Y) : nativeExterior X Y T ((Cor.graphFunctor k).map φ) =
    (Cor.graphFunctor k).map (SmoothSite.productMap φ (𝟙 T)) :=
  nativeExterior_graphFunctor X Y T φ
example : nativeExterior X X T (𝟙 (Cor.mk X)) = 𝟙 (Cor.mk (SmoothSite.product X T)) :=
  nativeExterior_id X T

example (φ : X ⟶ Y) (n : ℤ) :
    nativeExterior X Y T (n • (Cor.graphFunctor k).map φ) =
      n • (Cor.graphFunctor k).map (SmoothSite.productMap φ (𝟙 T)) := by
  rw [nativeExterior_zsmul, nativeExterior_graphFunctor]

example (φ : X ⟶ Y) :
    nativeExterior X Y T (-(Cor.graphFunctor k).map φ) =
      -(Cor.graphFunctor k).map (SmoothSite.productMap φ (𝟙 T)) := by
  rw [nativeExterior_neg, nativeExterior_graphFunctor]
