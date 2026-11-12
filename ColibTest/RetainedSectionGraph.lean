/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Divisors.RetainedSectionGraph

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace ColibTest

open Stacks.Chow

variable {C U V Y S : Scheme.{u}} [IsNoetherian U] [IsNoetherian V] [IsReduced V]
  (p : V ⟶ S) (t : Y ⟶ S) [IsSeparated t] [LocallyOfFiniteType t]
  (q : C ⟶ V) [IsSeparated q] (j : U ⟶ C) [IsOpenImmersion j]
  (r : U ⟶ pullback p t) (hr : r ≫ pullback.fst p t = j ≫ q)
  (s : V ⟶ C) (hs : s ≫ q = 𝟙 V) (sU : V ⟶ U) (hsU : sU ≫ j = s)
  (hI : Set.range s.ker.subschemeι ⊆ Set.range j)
  [Stacks.Morphisms.IsFiniteLocallyFree (s.ker.subschemeι ≫ q)]

example :
    retainedFiniteFlatDivisorCorrespondence p t q j r hr s.ker hI =
      graphCorrespondenceOfComponents p t (sU ≫ r ≫ pullback.snd p t)
        (sectionTarget_base p t r sU (retainedSection_firstProjection p t q j r hr s hs sU hsU))
        (AlgebraicCycle.fundamentalCycle_genericPoints_finite V) :=
  retainedFiniteFlatDivisorCorrespondence_sectionKernel p t q j r hr s hs sU hsU hI

end ColibTest

#print axioms Stacks.Chow.retainedFiniteFlatDivisorCorrespondence_sectionKernel
