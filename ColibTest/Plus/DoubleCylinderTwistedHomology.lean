/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.Topology.LocalCoefficients.DoubleCylinderTwistedHomology

/-! Regression tests for both actual end maps with arbitrary local coefficients. -/

open CategoryTheory MonoidalCategory
open FundamentalGroupoid.LocalCoefficients TopCat.DoubleCylinder
open scoped unitInterval

universe u

section
variable {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
  {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
  (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)
  (lo hi : unitInterval) (b : Band lo hi) (V : System.{u, u} D)

example (hf : ∀ L : System.{u, u} B, QuasiIso (UniverseLift.chainMap f.hom L)) :
    QuasiIso (UniverseLift.chainMap (gapRightEndpoint e) V) :=
  doubleCylinder_rightEnd_universeLift_quasiIso f g sq lo hi b hf V

example (hg : ∀ L : System.{u, u} C, QuasiIso (UniverseLift.chainMap g.hom L)) :
    QuasiIso (UniverseLift.chainMap (gapLeftEndpoint e) V) :=
  doubleCylinder_leftEnd_universeLift_quasiIso f g sq lo hi b hg V

example (hf : ∀ L : System.{u, u} B, QuasiIso (pushforwardChainMap f.hom L)) :
    (relativeSingularChainComplex (rightCollarSet f g sq lo) V).Acyclic :=
  doubleCylinder_rightCollar_twisted_relative_acyclic f g sq lo hi b hf V

end
