/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Basic

/-!
# The actual incidence scheme of two finite correspondences

The incidence scheme is the fibre product of the two native integral closed subschemes
along their maps to the middle scheme. Its map to the outer product is finite when the
second correspondence is finite over the middle scheme, the first is finite over the
source, and the final scheme is separated over the base. No cycle multiplicity is
assigned here: in particular the fundamental cycle of this fibre product is not silently
substituted for the Tor intersection cycle.

This is the geometric input to the composition formula in
`kangxyz/motivic` at `a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/AlgebraicGeometry/Correspondences/Composition/Support/Basic.lean`.
The downstream consumer is `Composition/Incidence/TorCycle.lean`.
The integral closed subschemes and finite-morphism cancellation are used directly from
Stacks and Mathlib. Tor multiplicities are treated in Stacks, Tags 0AZR and 0B08;
no claim of composition associativity is made in this file.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)

/-- The actual fibre product of the two integral supports over the middle scheme. -/
abbrev correspondenceIncidence
    (z : (pullback (C := Scheme) f g)) (w : (pullback (C := Scheme) g h)) : Scheme.{u} :=
  pullback ((integralComponentAt z).subschemeι ≫ pullback.snd f g)
    ((integralComponentAt w).subschemeι ≫ pullback.fst g h)

/-- The first projection of the incidence scheme to the source. -/
def correspondenceIncidenceLeft
    (z : (pullback (C := Scheme) f g)) (w : (pullback (C := Scheme) g h)) :
    correspondenceIncidence f g h z w ⟶ X :=
  pullback.fst _ _ ≫ (integralComponentAt z).subschemeι ≫ pullback.fst f g

/-- The second projection of the incidence scheme to the final target. -/
def correspondenceIncidenceRight
    (z : (pullback (C := Scheme) f g)) (w : (pullback (C := Scheme) g h)) :
    correspondenceIncidence f g h z w ⟶ Z :=
  pullback.snd _ _ ≫ (integralComponentAt w).subschemeι ≫ pullback.snd g h

/-- The two actual incidence projections have the same composite to the base. -/
theorem correspondenceIncidence_condition
    (z : (pullback (C := Scheme) f g)) (w : (pullback (C := Scheme) g h)) :
    correspondenceIncidenceLeft f g h z w ≫ f =
      correspondenceIncidenceRight f g h z w ≫ h := by
  simp only [correspondenceIncidenceLeft, correspondenceIncidenceRight, Category.assoc]
  calc
    _ = (pullback.fst _ _ ≫ ((integralComponentAt z).subschemeι ≫
        pullback.snd f g)) ≫ g := by
      simp only [Category.assoc, pullback.condition (f := f) (g := g)]
    _ = (pullback.snd _ _ ≫ ((integralComponentAt w).subschemeι ≫
        pullback.fst g h)) ≫ g :=
      congrArg (fun t => t ≫ g)
        (pullback.condition (f := (integralComponentAt z).subschemeι ≫ pullback.snd f g)
          (g := (integralComponentAt w).subschemeι ≫ pullback.fst g h))
    _ = _ := by simp only [Category.assoc, pullback.condition (f := g) (g := h)]

/-- The original incidence map to the product of source and final target. -/
def correspondenceIncidenceMap
    (z : (pullback (C := Scheme) f g)) (w : (pullback (C := Scheme) g h)) :
    correspondenceIncidence f g h z w ⟶ pullback f h :=
  pullback.lift (correspondenceIncidenceLeft f g h z w)
    (correspondenceIncidenceRight f g h z w) (correspondenceIncidence_condition f g h z w)

@[reassoc (attr := simp)]
theorem correspondenceIncidenceMap_fst
    (z : (pullback (C := Scheme) f g)) (w : (pullback (C := Scheme) g h)) :
    correspondenceIncidenceMap f g h z w ≫ pullback.fst f h =
      correspondenceIncidenceLeft f g h z w := by
  simp [correspondenceIncidenceMap]

@[reassoc (attr := simp)]
theorem correspondenceIncidenceMap_snd
    (z : (pullback (C := Scheme) f g)) (w : (pullback (C := Scheme) g h)) :
    correspondenceIncidenceMap f g h z w ≫ pullback.snd f h =
      correspondenceIncidenceRight f g h z w := by
  simp [correspondenceIncidenceMap]

/-- Finiteness of the actual incidence map, not merely of its image support. -/
theorem isFinite_correspondenceIncidenceMap [IsSeparated h]
    (z : (pullback (C := Scheme) f g)) (w : (pullback (C := Scheme) g h))
    (hz : IsFiniteCorrespondencePoint f g z)
    (hw : IsFiniteCorrespondencePoint g h w) :
    IsFinite (correspondenceIncidenceMap f g h z w) := by
  let : IsFinite ((integralComponentAt z).subschemeι ≫ pullback.fst f g) := hz.1
  let : IsFinite ((integralComponentAt w).subschemeι ≫ pullback.fst g h) := hw.1
  have : IsFinite (correspondenceIncidenceLeft f g h z w) := by
    dsimp [correspondenceIncidenceLeft]
    infer_instance
  have : IsFinite (correspondenceIncidenceMap f g h z w ≫ pullback.fst f h) := by
    simpa only [correspondenceIncidenceMap_fst] using
      (inferInstance : IsFinite (correspondenceIncidenceLeft f g h z w))
  exact IsFinite.of_comp (correspondenceIncidenceMap f g h z w) (pullback.fst f h)

end Stacks.Chow
