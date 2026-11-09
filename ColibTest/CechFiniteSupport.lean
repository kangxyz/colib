/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Nisnevich.Cech.FiniteSupport

/-!
# Native correspondence consumer of the common finite image

This combines the native correspondence support, common-image construction and
actual graph-incidence factors. The whole incidence and the whole common-support
pullback remain the actual categorical schemes throughout.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

variable {S X V Y U : Scheme.{u}}
  (x : X ⟶ S) (v : V ⟶ S) (y : Y ⟶ S) (q : V ⟶ Y) (hq : q ≫ y = v)
  (u : U ⟶ S) (g : U ⟶ X) (hg : g ≫ x = u)
  [IsSeparated x] [IsSeparated y] [LocallyOfFiniteType y]

example (c : finiteCorrespondences x v) (hne : c.1.support.Nonempty) :
    ∃ (C : Scheme.{u}) (j : C ⟶ pullback x y),
      IsClosedImmersion j ∧ IsFinite (j ≫ pullback.fst x y) ∧
      ∀ (a : pullback (C := Scheme) x v), a ∈ c.1.support →
        ∃ r : (integralComponentAt a).subscheme ⟶ C,
        r ≫ j = correspondenceGraphPostcompositionMap x v y q hq a ∧
        ∀ t : genericPoints U, ∃ e :
            correspondenceIncidence u x v (correspondenceGraphMap u x g hg t.val) a ⟶
              pullback (j ≫ pullback.fst x y) g,
          IsFinite e ∧
          e ≫ pullback.fst (j ≫ pullback.fst x y) g = pullback.snd _ _ ≫ r ∧
          e ≫ pullback.snd (j ≫ pullback.fst x y) g =
            correspondenceIncidenceLeft u x v (correspondenceGraphMap u x g hg t.val) a ∧
          e ≫ pullback.fst (j ≫ pullback.fst x y) g ≫ j ≫ pullback.snd x y =
            correspondenceIncidenceRight u x v (correspondenceGraphMap u x g hg t.val) a ≫ q := by
  obtain ⟨C, j, hj, hfinite, hr⟩ :=
    exists_common_finite_image_of_correspondence x v y q hq c hne
  let : IsFinite (j ≫ pullback.fst x y) := hfinite
  refine ⟨C, j, hj, hfinite, ?_⟩
  intro a ha
  obtain ⟨r, hr⟩ := hr a ha
  refine ⟨r, hr, ?_⟩
  intro t
  refine ⟨graphIncidenceToCommonSupport x v y q hq a j r hr u g hg t, ?_, ?_, ?_, ?_⟩
  · exact isFinite_graphIncidenceToCommonSupport x v y q hq a j r hr u g hg t (c.2.2 a ha)
  · exact graphIncidenceToCommonSupport_fst x v y q hq a j r hr u g hg t
  · exact graphIncidenceToCommonSupport_snd x v y q hq a j r hr u g hg t
  · exact graphIncidenceToCommonSupport_target x v y q hq a j r hr u g hg t

example {C : Scheme.{u}} (a : pullback (C := Scheme) x v) (j : C ⟶ pullback x y)
    (r : (integralComponentAt a).subscheme ⟶ C)
    (hr : r ≫ j = correspondenceGraphPostcompositionMap x v y q hq a)
    (t : genericPoints U) :
    graphIncidenceToCommonSupport x v y q hq a j r hr u g hg t ≫
      ClosedImageBaseChange.inclusion x y u g hg j =
        correspondenceIncidenceMap u x v (correspondenceGraphMap u x g hg t.val) a ≫
          pullback.map u v u y (𝟙 U) q (𝟙 S) (by simp) (by simpa using hq.symm) :=
  graphIncidenceToCommonSupport_inclusion x v y q hq a j r hr u g hg t
