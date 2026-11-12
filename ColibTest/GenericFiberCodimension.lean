/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Morphisms.Smooth.GenericFiberCodimension

/-! # Original-source codimension over a generic base point -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

example {X S : Scheme.{u}} (q : X ⟶ S) [IsReduced S]
    (x : X) (hx : q x ∈ genericPoints S) (b : X.presheaf.stalk x) :
    stalkEquivFiberStalkOfGeneric q x hx b =
      ((q.fiberι (q x)).stalkMap (q.asFiber x)).hom
        ((X.presheaf.stalkCongr (.of_eq (q.fiberι_asFiber x).symm)).hom b) :=
  stalkEquivFiberStalkOfGeneric_apply q x hx b

example {X S : Scheme.{u}} (q : X ⟶ S) [IsReduced S] (n : ℕ)
    [SmoothOfRelativeDimension n q] [IsSeparated q] (x : X)
    (hx : q x ∈ genericPoints S) (hf : (q.residueFieldMap x).hom.Finite) :
    Order.coheight x = n :=
  coheight_eq_of_image_mem_genericPoints_finite_residue q n x hx hf

example {D X S : Scheme.{u}} (i : D ⟶ X) [IsClosedImmersion i]
    (q : X ⟶ S) [IsReduced S] [SmoothOfRelativeDimension 1 q] [IsSeparated q]
    [IsFinite (i ≫ q)] (x : D) (hx : q (i x) ∈ genericPoints S) :
    Order.coheight (i x) = 1 :=
  coheight_eq_of_image_mem_genericPoints_finite_closed_support i q 1 x hx

example {D X S : Scheme.{u}} (i : D ⟶ X) [IsClosedImmersion i]
    (q : X ⟶ S) [IsReduced S] [SmoothOfRelativeDimension 1 q] [IsSeparated q]
    [IsFinite (i ≫ q)] (x : D) :
    Order.coheight (i x) = 1 ↔ q (i x) ∈ genericPoints S :=
  coheight_eq_one_iff_image_mem_genericPoints_of_finite_closed_support i q x

#print axioms stalkEquivFiberStalkOfGeneric
#print axioms stalkEquivFiberStalkOfGeneric_apply
#print axioms coheight_eq_of_image_mem_genericPoints_closed_fiber
#print axioms coheight_eq_of_image_mem_genericPoints_finite_residue
#print axioms coheight_eq_of_image_mem_genericPoints_finite_closed_support
#print axioms coheight_eq_one_iff_image_mem_genericPoints_of_finite_closed_support

end AlgebraicGeometry.Scheme
