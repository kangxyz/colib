/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Graph.Incidence

/-! Ten freshly reconstructed test examples for the historical graph-incidence surface.
These are not the lost test bytes and have not been compiled in this recovery task. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Function.locallyFinsuppWithin

attribute [local instance] Classical.propDecidable

universe u

namespace Stacks.Chow

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
  (φ : X ⟶ Y) (hφ : φ ≫ g = f) (ψ : Y ⟶ Z) (hψ : ψ ≫ h = g)

example [IsSeparated g] (t : X) :
    ∃ e : (integralComponentAt t).subscheme ≅
        (integralComponentAt (correspondenceGraphMap f g φ hφ t)).subscheme,
      e.hom ≫ (integralComponentAt (correspondenceGraphMap f g φ hφ t)).subschemeι ≫
          pullback.fst f g = (integralComponentAt t).subschemeι ∧
      e.hom ≫ (integralComponentAt (correspondenceGraphMap f g φ hφ t)).subschemeι ≫
          pullback.snd f g = (integralComponentAt t).subschemeι ≫ φ :=
  exists_iso_integralComponentAt_graphMap f g φ hφ t

example [IsSeparated g] (t : X) :
    IsClosedImmersion ((integralComponentAt (correspondenceGraphMap f g φ hφ t)).subschemeι ≫
      pullback.fst f g) :=
  isClosedImmersion_integralComponentAt_graphMap_fst f g φ hφ t

example [IsSeparated g] (t : X) :
    Set.range ((integralComponentAt (correspondenceGraphMap f g φ hφ t)).subschemeι ≫
      pullback.fst f g) = closure {t} :=
  range_integralComponentAt_graphMap_fst f g φ hφ t

example [IsSeparated g] (t : X) :
    (integralComponentAt (correspondenceGraphMap f g φ hφ t)).subschemeι ≫ pullback.snd f g =
      (integralComponentAt (correspondenceGraphMap f g φ hφ t)).subschemeι ≫
        pullback.fst f g ≫ φ :=
  integralComponentAt_graphMap_snd f g φ hφ t

example [IsSeparated h] (z : pullback (C := Scheme) f g) (t : Y) :
    correspondenceIncidenceMap f g h z (correspondenceGraphMap g h ψ hψ t) =
      pullback.fst _ _ ≫ (integralComponentAt z).subschemeι ≫
        pullback.map f g f h (𝟙 X) ψ (𝟙 S) (by simp) (by simpa using hψ.symm) :=
  correspondenceIncidenceMap_graphMap_right f g h ψ hψ z t

example [IsSeparated h] (z : pullback (C := Scheme) f g) (t : Y)
    (hz : Set.range ((integralComponentAt z).subschemeι ≫ pullback.snd f g) ⊆ closure {t}) :
    IsIso (pullback.fst ((integralComponentAt z).subschemeι ≫ pullback.snd f g)
      ((integralComponentAt (correspondenceGraphMap g h ψ hψ t)).subschemeι ≫ pullback.fst g h)) :=
  isIso_correspondenceIncidence_fst_graphMap_of_range_subset f g h ψ hψ z t hz

example [IsSeparated h] (z : pullback (C := Scheme) f g) (t : Y)
    (hz : Set.range ((integralComponentAt z).subschemeι ≫ pullback.snd f g) ⊆ closure {t}) :
    (correspondenceIncidenceGraphIso f g h ψ hψ z t hz).inv ≫
        correspondenceIncidenceMap f g h z (correspondenceGraphMap g h ψ hψ t) =
      (integralComponentAt z).subschemeι ≫
        pullback.map f g f h (𝟙 X) ψ (𝟙 S) (by simp) (by simpa using hψ.symm) :=
  correspondenceIncidenceGraphIso_inv_map f g h ψ hψ z t hz

example [IsSeparated g] (z : pullback (C := Scheme) f g) (t : Y) :
    correspondenceIncidenceMap f g g z (correspondenceGraphMap g g (𝟙 Y) (by simp) t) =
      pullback.fst _ _ ≫ (integralComponentAt z).subschemeι :=
  correspondenceIncidenceMap_diagonal_right f g z t

example [IsSeparated f] (t : X) (z : pullback (C := Scheme) f g)
    (hz : Set.range ((integralComponentAt z).subschemeι ≫ pullback.fst f g) ⊆ closure {t}) :
    IsIso (pullback.snd
      ((integralComponentAt (correspondenceGraphMap f f (𝟙 X) (by simp) t)).subschemeι ≫
        pullback.snd f f)
      ((integralComponentAt z).subschemeι ≫ pullback.fst f g)) ∧
    correspondenceIncidenceMap f f g (correspondenceGraphMap f f (𝟙 X) (by simp) t) z =
      pullback.snd _ _ ≫ (integralComponentAt z).subschemeι :=
  ⟨isIso_correspondenceIncidence_snd_diagonal_of_range_subset f g t z hz,
    correspondenceIncidenceMap_diagonal_left f g t z⟩

example [IsSeparated h] [IsIntegral Y] (z : pullback (C := Scheme) f (ψ ≫ h)) :
    ∃ w : pullback (C := Scheme) (ψ ≫ h) h,
      (graphFiniteCorrespondence ψ h).1 = single w 1 ∧
      integralComponentAt w =
        (pullback.lift (𝟙 Y) ψ (by simp) : Y ⟶ pullback (C := Scheme) (ψ ≫ h) h).ker ∧
      IsIso (pullback.fst ((integralComponentAt z).subschemeι ≫ pullback.snd f (ψ ≫ h))
        ((integralComponentAt w).subschemeι ≫ pullback.fst (ψ ≫ h) h)) ∧
      correspondenceIncidenceMap f (ψ ≫ h) h z w =
        pullback.fst _ _ ≫ (integralComponentAt z).subschemeι ≫
          pullback.map f (ψ ≫ h) f h (𝟙 X) ψ (𝟙 S) (by simp) (by simp) :=
  exists_graphFiniteCorrespondence_incidence f h ψ z

end Stacks.Chow
