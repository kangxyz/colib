/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.Components
public import Colib.AlgebraicGeometry.Correspondences.Incidence
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Actual incidence with a graph component

The graph support is the native integral component at an actual graph image point.
Native closed-subscheme uniqueness identifies it with the original source component,
with both projection equations. If an integral support maps into that component,
its actual incidence projection is an isomorphism: it is a surjective closed
immersion into the reduced integral support. Normality is not needed for this
surviving-component result. The outer map is identified explicitly, not merely
up to an unspecified incidence isomorphism.

The final two lemmas are explicitly integral-source whole-graph specializations.
They use the exact graph ideal and prime cycle from the existing Graph file.
They do not narrow the all-component correspondence construction.

Source provenance: `motivic_source_a6805c4`, revision
`a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/AlgebraicGeometry/Correspondences/Composition/Identity/Tor.lean` and
`Identity/Units.lean`. Mathematical context: MVW (2006), Lecture 1, Example 1.2
on printed p. 3, diagonal and composition discussion on p. 4, graph functor
paragraph on p. 6. Only the geometric inputs are supplied, not Tor multiplicities,
unit laws, graph functoriality, or associativity.

Recovery status: fresh reconstruction from the retained declaration/proof outline;
not the lost historical bytes, and not compiled in this recovery task.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Function.locallyFinsuppWithin

attribute [local instance] Classical.propDecidable

universe u

namespace Stacks.Chow

section GraphComponent

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
  (φ : X ⟶ Y) (hφ : φ ≫ g = f) [IsSeparated g]

/-- The native source component and actual graph component are isomorphic, with both projections. -/
theorem exists_iso_integralComponentAt_graphMap (t : X) :
    ∃ e : (integralComponentAt t).subscheme ≅
        (integralComponentAt (correspondenceGraphMap f g φ hφ t)).subscheme,
      e.hom ≫ (integralComponentAt (correspondenceGraphMap f g φ hφ t)).subschemeι ≫
          pullback.fst f g = (integralComponentAt t).subschemeι ∧
      e.hom ≫ (integralComponentAt (correspondenceGraphMap f g φ hφ t)).subschemeι ≫
          pullback.snd f g = (integralComponentAt t).subschemeι ≫ φ := by
  let : IsClosedImmersion (correspondenceGraphMap f g φ hφ) :=
    isClosedImmersion_correspondenceGraphMap f g φ hφ
  obtain ⟨e, he⟩ := Stacks.ChernCap42.exists_iso_integralComponentAt
    (correspondenceGraphMap f g φ hφ) t
  refine ⟨e, ?_, ?_⟩
  · simpa only [Category.assoc, correspondenceGraphMap_fst, Category.comp_id] using
      congrArg (fun k => k ≫ pullback.fst f g) he
  · simpa only [Category.assoc, correspondenceGraphMap_snd] using
      congrArg (fun k => k ≫ pullback.snd f g) he

/-- The graph component's actual source projection is a closed immersion. -/
theorem isClosedImmersion_integralComponentAt_graphMap_fst (t : X) :
    IsClosedImmersion ((integralComponentAt (correspondenceGraphMap f g φ hφ t)).subschemeι ≫
      pullback.fst f g) := by
  obtain ⟨e, hf, _⟩ := exists_iso_integralComponentAt_graphMap f g φ hφ t
  have heq : (integralComponentAt (correspondenceGraphMap f g φ hφ t)).subschemeι ≫
      pullback.fst f g = e.inv ≫ (integralComponentAt t).subschemeι := by
    apply (cancel_epi e.hom).mp
    simpa only [Iso.hom_inv_id_assoc] using hf
  rw [heq]
  infer_instance

/-- The actual graph component source projection has exactly the original point closure as image. -/
theorem range_integralComponentAt_graphMap_fst (t : X) :
    Set.range ((integralComponentAt (correspondenceGraphMap f g φ hφ t)).subschemeι ≫
      pullback.fst f g) = closure {t} := by
  obtain ⟨e, hf, _⟩ := exists_iso_integralComponentAt_graphMap f g φ hφ t
  rw [← range_eq_range_of_surjective (integralComponentAt t).subschemeι _ e.hom hf,
    Scheme.IdealSheafData.range_subschemeι, coe_support_integralComponentAt]

/-- The actual target projection is the source projection followed by the given morphism. -/
@[reassoc]
theorem integralComponentAt_graphMap_snd (t : X) :
    (integralComponentAt (correspondenceGraphMap f g φ hφ t)).subschemeι ≫ pullback.snd f g =
      (integralComponentAt (correspondenceGraphMap f g φ hφ t)).subschemeι ≫
        pullback.fst f g ≫ φ := by
  obtain ⟨e, hf, hg⟩ := exists_iso_integralComponentAt_graphMap f g φ hφ t
  apply (cancel_epi e.hom).mp
  calc
    _ = (integralComponentAt t).subschemeι ≫ φ := hg
    _ = (e.hom ≫
        (integralComponentAt (correspondenceGraphMap f g φ hφ t)).subschemeι ≫
        pullback.fst f g) ≫ φ := by rw [hf]
    _ = _ := by simp only [Category.assoc]

end GraphComponent

section RightGraph

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
  (ψ : Y ⟶ Z) (hψ : ψ ≫ h = g) [IsSeparated h]
  (z : pullback (C := Scheme) f g) (t : Y)

/-- The actual right graph incidence map has the original support's induced outer map. -/
theorem correspondenceIncidenceMap_graphMap_right :
    correspondenceIncidenceMap f g h z (correspondenceGraphMap g h ψ hψ t) =
      pullback.fst _ _ ≫ (integralComponentAt z).subschemeι ≫
        pullback.map f g f h (𝟙 X) ψ (𝟙 S) (by simp) (by simpa using hψ.symm) := by
  apply pullback.hom_ext
  · simp [correspondenceIncidenceLeft, pullback.map]
  · simp only [correspondenceIncidenceMap_snd, correspondenceIncidenceRight,
      Category.assoc, pullback.map, pullback.lift_snd]
    rw [integralComponentAt_graphMap_snd]
    simpa only [Category.assoc] using
      congrArg (fun k => k ≫ ψ)
        (pullback.condition
          (f := (integralComponentAt z).subschemeι ≫ pullback.snd f g)
          (g := (integralComponentAt (correspondenceGraphMap g h ψ hψ t)).subschemeι ≫
            pullback.fst g h)).symm

/-- Actual component containment, without normality, makes the surviving incidence projection iso. -/
theorem isIso_correspondenceIncidence_fst_graphMap_of_range_subset
    (hz : Set.range ((integralComponentAt z).subschemeι ≫ pullback.snd f g) ⊆ closure {t}) :
    IsIso (pullback.fst ((integralComponentAt z).subschemeι ≫ pullback.snd f g)
      ((integralComponentAt (correspondenceGraphMap g h ψ hψ t)).subschemeι ≫
        pullback.fst g h)) := by
  let : IsClosedImmersion
      ((integralComponentAt (correspondenceGraphMap g h ψ hψ t)).subschemeι ≫ pullback.fst g h) :=
    isClosedImmersion_integralComponentAt_graphMap_fst g h ψ hψ t
  let : IsIntegral (integralComponentAt z).subscheme := isIntegral_integralComponentAt z
  let : Surjective (pullback.fst ((integralComponentAt z).subschemeι ≫ pullback.snd f g)
      ((integralComponentAt (correspondenceGraphMap g h ψ hψ t)).subschemeι ≫
        pullback.fst g h)) := ⟨by
    intro x
    have hx : x ∈ Set.range (pullback.fst
        ((integralComponentAt z).subschemeι ≫ pullback.snd f g)
        ((integralComponentAt (correspondenceGraphMap g h ψ hψ t)).subschemeι ≫
          pullback.fst g h)) := by
      rw [Scheme.Pullback.range_fst, range_integralComponentAt_graphMap_fst]
      exact hz ⟨x, rfl⟩
    exact hx⟩
  exact isIso_of_isClosedImmersion_of_surjective _

/-- The isomorphism is the actual first incidence projection, not additional input data. -/
def correspondenceIncidenceGraphIso
    (hz : Set.range ((integralComponentAt z).subschemeι ≫ pullback.snd f g) ⊆ closure {t}) :
    correspondenceIncidence f g h z (correspondenceGraphMap g h ψ hψ t) ≅
      (integralComponentAt z).subscheme := by
  let := isIso_correspondenceIncidence_fst_graphMap_of_range_subset f g h ψ hψ z t hz
  exact asIso (pullback.fst _ _)

/-- Transporting the actual incidence outer map across the constructed inverse gives the support map. -/
@[reassoc]
theorem correspondenceIncidenceGraphIso_inv_map
    (hz : Set.range ((integralComponentAt z).subschemeι ≫ pullback.snd f g) ⊆ closure {t}) :
    (correspondenceIncidenceGraphIso f g h ψ hψ z t hz).inv ≫
        correspondenceIncidenceMap f g h z (correspondenceGraphMap g h ψ hψ t) =
      (integralComponentAt z).subschemeι ≫
        pullback.map f g f h (𝟙 X) ψ (𝟙 S) (by simp) (by simpa using hψ.symm) := by
  rw [correspondenceIncidenceMap_graphMap_right]
  change (correspondenceIncidenceGraphIso f g h ψ hψ z t hz).inv ≫
      (correspondenceIncidenceGraphIso f g h ψ hψ z t hz).hom ≫ _ = _
  simp

end RightGraph

section Diagonal

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- The right diagonal component incidence has exactly the original support's outer map. -/
theorem correspondenceIncidenceMap_diagonal_right [IsSeparated g]
    (z : pullback (C := Scheme) f g) (t : Y) :
    correspondenceIncidenceMap f g g z (correspondenceGraphMap g g (𝟙 Y) (by simp) t) =
      pullback.fst _ _ ≫ (integralComponentAt z).subschemeι := by
  simpa [pullback.map] using
    correspondenceIncidenceMap_graphMap_right f g g (𝟙 Y) (by simp) z t

/-- The left diagonal component incidence has exactly the original support's outer map. -/
theorem correspondenceIncidenceMap_diagonal_left [IsSeparated f]
    (t : X) (z : pullback (C := Scheme) f g) :
    correspondenceIncidenceMap f f g (correspondenceGraphMap f f (𝟙 X) (by simp) t) z =
      pullback.snd _ _ ≫ (integralComponentAt z).subschemeι := by
  have hdiag := integralComponentAt_graphMap_snd f f (𝟙 X) (by simp) t
  simp only [Category.comp_id] at hdiag
  apply pullback.hom_ext
  · simp only [correspondenceIncidenceMap_fst, correspondenceIncidenceLeft, Category.assoc]
    rw [← hdiag]
    exact pullback.condition
  · simp [correspondenceIncidenceRight]

/-- Actual source-component containment makes the surviving left diagonal incidence projection iso. -/
theorem isIso_correspondenceIncidence_snd_diagonal_of_range_subset [IsSeparated f]
    (t : X) (z : pullback (C := Scheme) f g)
    (hz : Set.range ((integralComponentAt z).subschemeι ≫ pullback.fst f g) ⊆ closure {t}) :
    IsIso (pullback.snd
      ((integralComponentAt (correspondenceGraphMap f f (𝟙 X) (by simp) t)).subschemeι ≫
        pullback.snd f f)
      ((integralComponentAt z).subschemeι ≫ pullback.fst f g)) := by
  have hdiag := integralComponentAt_graphMap_snd f f (𝟙 X) (by simp) t
  simp only [Category.comp_id] at hdiag
  let : IsClosedImmersion
      ((integralComponentAt (correspondenceGraphMap f f (𝟙 X) (by simp) t)).subschemeι ≫
        pullback.snd f f) := by
    rw [hdiag]
    exact isClosedImmersion_integralComponentAt_graphMap_fst f f (𝟙 X) (by simp) t
  let : IsIntegral (integralComponentAt z).subscheme := isIntegral_integralComponentAt z
  let : Surjective (pullback.snd
      ((integralComponentAt (correspondenceGraphMap f f (𝟙 X) (by simp) t)).subschemeι ≫
        pullback.snd f f)
      ((integralComponentAt z).subschemeι ≫ pullback.fst f g)) := ⟨by
    intro x
    have hx : x ∈ Set.range (pullback.snd
        ((integralComponentAt (correspondenceGraphMap f f (𝟙 X) (by simp) t)).subschemeι ≫
          pullback.snd f f)
        ((integralComponentAt z).subschemeι ≫ pullback.fst f g)) := by
      rw [Scheme.Pullback.range_snd, hdiag, range_integralComponentAt_graphMap_fst]
      exact hz ⟨x, rfl⟩
    exact hx⟩
  exact isIso_of_isClosedImmersion_of_surjective _

end Diagonal

section WholeGraph

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (h : Z ⟶ S) (ψ : Y ⟶ Z) [IsSeparated h]

/-- Equality with the actual graph ideal gives the actual incidence iso and its outer map. -/
theorem correspondenceIncidence_of_graphIdeal
    (z : pullback (C := Scheme) f (ψ ≫ h)) (w : pullback (C := Scheme) (ψ ≫ h) h)
    (hw : integralComponentAt w =
      (pullback.lift (𝟙 Y) ψ (by simp) : Y ⟶ pullback (C := Scheme) (ψ ≫ h) h).ker) :
    IsIso (pullback.fst ((integralComponentAt z).subschemeι ≫ pullback.snd f (ψ ≫ h))
      ((integralComponentAt w).subschemeι ≫ pullback.fst (ψ ≫ h) h)) ∧
    correspondenceIncidenceMap f (ψ ≫ h) h z w =
      pullback.fst _ _ ≫ (integralComponentAt z).subschemeι ≫
        pullback.map f (ψ ≫ h) f h (𝟙 X) ψ (𝟙 S) (by simp) (by simp) := by
  have hπ : IsIso ((integralComponentAt w).subschemeι ≫ pullback.fst (ψ ≫ h) h) := by
    rw [hw]
    exact isIso_graphImage_projection ψ h
  let : IsIso ((integralComponentAt w).subschemeι ≫ pullback.fst (ψ ≫ h) h) := hπ
  refine ⟨inferInstance, ?_⟩
  have hsnd : (integralComponentAt w).subschemeι ≫ pullback.snd (ψ ≫ h) h =
      (integralComponentAt w).subschemeι ≫ pullback.fst (ψ ≫ h) h ≫ ψ := by
    rw [hw]
    let j : Y ⟶ pullback (C := Scheme) (ψ ≫ h) h := pullback.lift (𝟙 Y) ψ (by simp)
    let : IsClosedImmersion j := isClosedImmersion_graphLift ψ h
    apply (cancel_epi j.toImage).mp
    simp [j, ← Category.assoc, Scheme.Hom.toImage_imageι]
  apply pullback.hom_ext
  · simp [correspondenceIncidenceLeft, pullback.map]
  · simp only [correspondenceIncidenceMap_snd, correspondenceIncidenceRight,
      Category.assoc, pullback.map, pullback.lift_snd]
    rw [hsnd]
    simpa only [Category.assoc] using congrArg (fun k => k ≫ ψ)
      (pullback.condition
        (f := (integralComponentAt z).subschemeι ≫ pullback.snd f (ψ ≫ h))
        (g := (integralComponentAt w).subschemeι ≫ pullback.fst (ψ ≫ h) h)).symm

/-- The actual integral graph prime cycle supplies its ideal and the corresponding geometric incidence. -/
theorem exists_graphFiniteCorrespondence_incidence [IsIntegral Y]
    (z : pullback (C := Scheme) f (ψ ≫ h)) :
    ∃ w : pullback (C := Scheme) (ψ ≫ h) h,
      (graphFiniteCorrespondence ψ h).1 = single w 1 ∧
      integralComponentAt w =
        (pullback.lift (𝟙 Y) ψ (by simp) : Y ⟶ pullback (C := Scheme) (ψ ≫ h) h).ker ∧
      IsIso (pullback.fst ((integralComponentAt z).subschemeι ≫ pullback.snd f (ψ ≫ h))
        ((integralComponentAt w).subschemeι ≫ pullback.fst (ψ ≫ h) h)) ∧
      correspondenceIncidenceMap f (ψ ≫ h) h z w =
        pullback.fst _ _ ≫ (integralComponentAt z).subschemeι ≫
          pullback.map f (ψ ≫ h) f h (𝟙 X) ψ (𝟙 S) (by simp) (by simp) := by
  obtain ⟨w, hc, hw⟩ := graphFiniteCorrespondence_prime ψ h
  exact ⟨w, hc, hw, correspondenceIncidence_of_graphIdeal f h ψ z w hw⟩

end WholeGraph

end Stacks.Chow
