/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Graph.NormalIncidence

/-! Eight freshly reconstructed tests for the historical normal/disconnected geometry surface.
These examples are uncompiled replacement sources, not inherited historical tests. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
  (φ : X ⟶ Y) (hφ : φ ≫ g = f) (ψ : Y ⟶ Z) (hψ : ψ ≫ h = g)

example [IsLocallyNoetherian X] [IsNormal X]
    (C : Set X) (hC : C ∈ irreducibleComponents X) : IsClopen C :=
  isClopen_of_mem_irreducibleComponents_of_isNormal C hC

example [IsLocallyNoetherian X] [IsNormal X]
    (C D : Set X) (hC : C ∈ irreducibleComponents X)
    (hD : D ∈ irreducibleComponents X) (hne : C ≠ D) : Disjoint C D :=
  disjoint_of_mem_irreducibleComponents_of_isNormal C D hC hD hne

example [IsLocallyNoetherian X] [IsNormal X] (t : genericPoints X) :
    IsOpenImmersion (integralComponentAt t.val).subschemeι :=
  isOpenImmersion_integralComponentAt_of_isNormal t

example [IsSeparated g] [IsLocallyNoetherian X] [IsNormal X] (t : genericPoints X) :
    IsOpenImmersion
      ((integralComponentAt (correspondenceGraphMap f g φ hφ t.val)).subschemeι ≫
        pullback.fst f g) :=
  isOpenImmersion_integralComponentAt_graphMap_fst f g φ hφ t

example [IsSeparated h] [IsLocallyNoetherian Y] [IsNormal Y]
    (z : pullback (C := Scheme) f g) (t : genericPoints Y) :
    IsOpenImmersion (pullback.fst ((integralComponentAt z).subschemeι ≫ pullback.snd f g)
      ((integralComponentAt (correspondenceGraphMap g h ψ hψ t.val)).subschemeι ≫
        pullback.fst g h)) :=
  isOpenImmersion_correspondenceIncidence_fst_graphMap f g h ψ hψ z t

example [IsSeparated h] [IsLocallyNoetherian Y] [IsNormal Y]
    (z : pullback (C := Scheme) f g) (s t : genericPoints Y) (hst : s ≠ t)
    (hz : Set.range ((integralComponentAt z).subschemeι ≫ pullback.snd f g) ⊆ closure {s.val}) :
    IsEmpty (correspondenceIncidence f g h z (correspondenceGraphMap g h ψ hψ t.val)) :=
  isEmpty_correspondenceIncidence_graphMap_of_ne f g h ψ hψ z s t hst hz

example [IsSeparated f] [IsLocallyNoetherian X] [IsNormal X]
    (t : genericPoints X) (z : pullback (C := Scheme) f g) :
    IsOpenImmersion (pullback.snd
      ((integralComponentAt (correspondenceGraphMap f f (𝟙 X) (by simp) t.val)).subschemeι ≫
        pullback.snd f f)
      ((integralComponentAt z).subschemeι ≫ pullback.fst f g)) :=
  isOpenImmersion_correspondenceIncidence_snd_diagonal f g t z

example [IsSeparated f] [IsLocallyNoetherian X] [IsNormal X]
    (z : pullback (C := Scheme) f g) (s t : genericPoints X) (hst : s ≠ t)
    (hz : Set.range ((integralComponentAt z).subschemeι ≫ pullback.fst f g) ⊆ closure {s.val}) :
    IsEmpty (correspondenceIncidence f f g
      (correspondenceGraphMap f f (𝟙 X) (by simp) t.val) z) :=
  isEmpty_correspondenceIncidence_diagonal_left_of_ne f g z s t hst hz

end Stacks.Chow
