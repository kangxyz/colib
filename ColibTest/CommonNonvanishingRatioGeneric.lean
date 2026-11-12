/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Divisors.Meromorphic.CommonNonvanishingRatioGeneric

/-! The common open is dense for actual regular meromorphic representatives. -/

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

attribute [local instance] AlgebraicGeometry.commonRatioGenericInvertible
  AlgebraicGeometry.commonRatioGenericQC

example {X : Scheme.{u}} [IsIntegral X] (P : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf P]
    (Up Uc : X.Opens) (hUp : genericPoint X ∈ Up) (hUc : genericPoint X ∈ Uc)
    (p : Γ(P, Up)) (c : Γ(P, Uc)) (s t : MeromorphicSection X.sheaf P)
    (hs : IsRegularMeromorphicSection X.sheaf P s)
    (ht : IsRegularMeromorphicSection X.sheaf P t)
    (hc : meromorphicGenericValue X P s = P.presheaf.germ Uc (genericPoint X) hUc c)
    (hp : meromorphicGenericValue X P t = P.presheaf.germ Up (genericPoint X) hUp p) :
    genericPoint X ∈ commonSectionNonvanishingOpen P Up Uc p c :=
  genericPoint_mem_commonSectionNonvanishingOpen P Up Uc hUp hUc p c s t hs ht hc hp

#print axioms AlgebraicGeometry.genericPoint_mem_commonSectionNonvanishingOpen
#print axioms AlgebraicGeometry.exists_denseOpen_unit_eq_meromorphicSectionRatio_boundary_one
