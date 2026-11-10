/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Scheme.GenericFiberLength

open CategoryTheory AlgebraicGeometry TopologicalSpace TensorProduct

noncomputable section
universe u v

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
  (hx : x ∈ genericPoints X) [IsReduced (f.fiber (f x))]

example : f.asFiber x ∈ genericPoints (f.fiber (f x)) :=
  f.asFiber_mem_genericPoints_of_mem_genericPoints x hx

example : Ideal.map (f.stalkMap x).hom
    (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
  f.map_maximalIdeal_stalkMap_of_mem_genericPoints x hx

example : Module.length (X.presheaf.stalk x)
    ((X.presheaf.stalk x) ⧸ Ideal.map (f.stalkMap x).hom
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)))) = 1 :=
  f.length_quotient_map_maximalIdeal_stalkMap x hx

example [Flat f] (y : Y) (hxy : f x = y) (M : Type v) [AddCommGroup M]
    [Module (Y.presheaf.stalk y) M] :
    letI := (f.stalkMapOverPoint x y hxy).toAlgebra
    Module.length (X.presheaf.stalk x) ((X.presheaf.stalk x) ⊗[Y.presheaf.stalk y] M) =
      Module.length (Y.presheaf.stalk y) M :=
  f.length_baseChange_stalkMapOverPoint x y hxy hx M

-- The field identification is induced by the actual fiber-inclusion stalk map.
example (b : X.presheaf.stalk x) :
    quotientStalkEquivFiberStalk f x
      (Ideal.Quotient.mk (Ideal.map (f.stalkMap x).hom
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)))) b) =
      ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom
        ((X.presheaf.stalkCongr (.of_eq (f.fiberι_asFiber x).symm)).hom b) :=
  quotientStalkEquivFiberStalk_mk f x b
