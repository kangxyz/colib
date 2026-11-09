/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Graph.IdentitySum

/-!
# Both full native Tor-pairing unit laws

Six regressions cover all signed finite cycles, explicitly finite
identity support, compact smooth identity support, and the actual empty-source
identity graph. Native leaf acceptance is recorded separately.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  [Smooth f] [Smooth g] [IsSeparated g]

example (hY : (genericPoints Y).Finite) (c : finiteCorrespondences f g) :
    incidenceTorPairing f g g c
      (graphCorrespondenceOfComponents g g (𝟙 Y) (Category.id_comp g) hY) = c :=
  incidenceTorPairing_graphIdentity_right f g hY c

example [IsSeparated f] (hX : (genericPoints X).Finite) (c : finiteCorrespondences f g) :
    incidenceTorPairing f f g
      (graphCorrespondenceOfComponents f f (𝟙 X) (Category.id_comp f) hX) c = c :=
  incidenceTorPairing_graphIdentity_left f g hX c

example [CompactSpace Y] (c : finiteCorrespondences f g) :
    incidenceTorPairing f g g c
      (graphCorrespondenceOfComponents g g (𝟙 Y) (Category.id_comp g)
        (finite_genericPoints_of_smooth_of_compact g)) = c :=
  incidenceTorPairing_graphIdentity_right f g (finite_genericPoints_of_smooth_of_compact g) c

example [IsSeparated f] [CompactSpace X] (c : finiteCorrespondences f g) :
    incidenceTorPairing f f g
      (graphCorrespondenceOfComponents f f (𝟙 X) (Category.id_comp f)
        (finite_genericPoints_of_smooth_of_compact f)) c = c :=
  incidenceTorPairing_graphIdentity_left f g (finite_genericPoints_of_smooth_of_compact f) c

example (hY : (genericPoints Y).Finite) (c : finiteCorrespondences f g) :
    incidenceTorPairing f g g (-c)
      (graphCorrespondenceOfComponents g g (𝟙 Y) (Category.id_comp g) hY) = -c :=
  incidenceTorPairing_graphIdentity_right f g hY (-c)

example [IsSeparated f] [IsEmpty X] (hX : (genericPoints X).Finite) :
    graphCorrespondenceOfComponents f f (𝟙 X) (Category.id_comp f) hX = 0 :=
  graphCorrespondenceOfComponents_eq_zero_of_isEmpty f f (𝟙 X) (Category.id_comp f) hX
