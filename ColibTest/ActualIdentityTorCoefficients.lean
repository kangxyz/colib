/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Graph.IdentityPrime

/-!
# Actual identity multiplicity and prime regressions

Seven examples cover both actual finite Tor coefficients, both
matching prime correspondences, both empty mismatches, and right graph incidence.
They impose neither a perfect field nor connected or integral ambient schemes.
Native leaf acceptance is recorded separately.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

variable {k : Type u} [Field k] {X Y Z : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))
  [Smooth f] [Smooth g] [Smooth h]

example [IsSeparated g] [IsSeparated h]
    (z : pullback (C := Scheme) f g) (ψ : Y ⟶ Z) (hψ : ψ ≫ h = g) (s : genericPoints Y)
    (t : genericPoints
      (correspondenceIncidence f g h z (correspondenceGraphMap g h ψ hψ s.val))) :
    correspondenceIncidenceTorCoefficient k f g h z
      (correspondenceGraphMap g h ψ hψ s.val) t = 1 :=
  correspondenceIncidenceTorCoefficient_graph_right_eq_one k f g h z ψ hψ s t

example [IsSeparated g] (z : pullback (C := Scheme) f g) (s : genericPoints Y)
    (t : genericPoints (correspondenceIncidence f g g z
      (correspondenceGraphMap g g (𝟙 Y) (Category.id_comp g) s.val))) :
    correspondenceIncidenceTorCoefficient k f g g z
      (correspondenceGraphMap g g (𝟙 Y) (Category.id_comp g) s.val) t = 1 :=
  correspondenceIncidenceTorCoefficient_identity_right_eq_one k f g z s t

example [IsSeparated f] (z : pullback (C := Scheme) f g) (s : genericPoints X)
    (t : genericPoints (correspondenceIncidence f f g
      (correspondenceGraphMap f f (𝟙 X) (Category.id_comp f) s.val) z)) :
    correspondenceIncidenceTorCoefficient k f f g
      (correspondenceGraphMap f f (𝟙 X) (Category.id_comp f) s.val) z t = 1 :=
  correspondenceIncidenceTorCoefficient_identity_left_eq_one k f g z s t

example [IsSeparated g] (z : pullback (C := Scheme) f g)
    (hz : IsFiniteCorrespondencePoint f g z) (s : genericPoints Y)
    (hs : Set.range ((integralComponentAt z).subschemeι ≫ pullback.snd f g) ⊆ closure {s.val}) :
    incidenceTorCorrespondence f g g z (correspondenceGraphMap g g (𝟙 Y) (Category.id_comp g) s.val)
      hz (isFiniteCorrespondencePoint_graphMap g g (𝟙 Y) (Category.id_comp g) s) =
      singleFiniteCorrespondence f g z hz 1 :=
  incidenceTorCorrespondence_identity_right_of_range_subset f g z hz s hs

example [IsSeparated f] [IsSeparated g] (z : pullback (C := Scheme) f g)
    (hz : IsFiniteCorrespondencePoint f g z) (s : genericPoints X)
    (hs : Set.range ((integralComponentAt z).subschemeι ≫ pullback.fst f g) ⊆ closure {s.val}) :
    incidenceTorCorrespondence f f g (correspondenceGraphMap f f (𝟙 X) (Category.id_comp f) s.val) z
      (isFiniteCorrespondencePoint_graphMap f f (𝟙 X) (Category.id_comp f) s) hz =
      singleFiniteCorrespondence f g z hz 1 :=
  incidenceTorCorrespondence_identity_left_of_range_subset f g z hz s hs

example [IsSeparated g] (z : pullback (C := Scheme) f g)
    (hz : IsFiniteCorrespondencePoint f g z) (s s' : genericPoints Y) (hss' : s ≠ s')
    (hs : Set.range ((integralComponentAt z).subschemeι ≫ pullback.snd f g) ⊆ closure {s.val}) :
    incidenceTorCorrespondence f g g z
      (correspondenceGraphMap g g (𝟙 Y) (Category.id_comp g) s'.val)
      hz (isFiniteCorrespondencePoint_graphMap g g (𝟙 Y) (Category.id_comp g) s') = 0 :=
  incidenceTorCorrespondence_identity_right_eq_zero_of_ne f g z hz s s' hss' hs

example [IsSeparated f] [IsSeparated g] (z : pullback (C := Scheme) f g)
    (hz : IsFiniteCorrespondencePoint f g z) (s s' : genericPoints X) (hss' : s ≠ s')
    (hs : Set.range ((integralComponentAt z).subschemeι ≫ pullback.fst f g) ⊆ closure {s.val}) :
    incidenceTorCorrespondence f f g
      (correspondenceGraphMap f f (𝟙 X) (Category.id_comp f) s'.val) z
      (isFiniteCorrespondencePoint_graphMap f f (𝟙 X) (Category.id_comp f) s') hz = 0 :=
  incidenceTorCorrespondence_identity_left_eq_zero_of_ne f g z hz s s' hss' hs
