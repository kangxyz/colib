/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.TripleStalkIdeal

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

noncomputable section

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  (t : correspondenceTripleIncidence f g h i z w v)

-- The native Tor object is defined before regularity and before finite-length assumptions.
example (n : ℕ) : ModuleCat (correspondenceTripleIncidenceAmbientStalk f g h i z w v t) :=
  correspondenceTripleIncidenceTor f g h i z w v t n

example [IsSeparated g] [IsSeparated h] :
    RingHom.ker ((correspondenceTripleIncidenceSixfoldInclusion f g h i z w v).stalkMap t).hom =
      correspondenceTripleIncidenceThreeStalkIdeals f g h i z w v t :=
  correspondenceTripleIncidenceSixfoldInclusion_stalkMap_ker f g h i z w v t

example [IsSeparated g] [IsSeparated h] :
    ModuleCat.of (correspondenceTripleIncidenceAmbientStalk f g h i z w v t)
      (correspondenceTripleIncidenceAmbientStalk f g h i z w v t ⧸
        correspondenceTripleIncidenceThreeStalkIdeals f g h i z w v t) ≅
      correspondenceTripleIncidenceStalkModule f g h i z w v t :=
  correspondenceTripleIncidenceStalkQuotientModuleIso f g h i z w v t

example [IsSeparated g] [IsSeparated h]
    (a : correspondenceTripleIncidenceAmbientStalk f g h i z w v t) :
    correspondenceTripleIncidenceStalkQuotientEquiv f g h i z w v t
        (Ideal.Quotient.mk (correspondenceTripleIncidenceThreeStalkIdeals f g h i z w v t) a) =
      ((correspondenceTripleIncidenceSixfoldInclusion f g h i z w v).stalkMap t).hom a :=
  correspondenceTripleIncidenceStalkQuotientEquiv_mk f g h i z w v t a
