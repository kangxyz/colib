/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Intersection.FlatProjectionStalkTor
public import Colib.AlgebraicGeometry.Intersection.OpenStalkComparison
public import Colib.AlgebraicGeometry.Correspondences.Graph.FlatFiber
public import Colib.AlgebraicGeometry.Correspondences.Graph.LeftPulledStalkTor
public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingProjection
public import Colib.AlgebraicGeometry.Correspondences.Composition.GlobalActualTorComparison

/-!
# Actual graph incidence stalk Tor over the original adjacent ambient

Flatness belongs to the projection from the triple ambient, not to the
integral correspondence support. Removing this projection retains the actual
right support stalk and the full left graph pullback stalk. For a closed graph
map their residue fields agree, so the every-degree comparison preserves full
module length. The graph pullback is identified with the original outer
ambient by its actual projections.

These are module and length comparisons before any cycle sum. Original order
weights, finite-pushforward residue degrees and image collisions are untouched.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
    [IsIntegral X] [IsSeparated g] (φ : X ⟶ Y) (hφ : φ ≫ g = f)
    (s : genericPoints X)

local notation "δ" => correspondenceGraphMap f g φ hφ s.val
local notation "L" => Scheme.IdealSheafData.subscheme
  (correspondenceLeftPulledIdeal f g h δ)
local notation "iL" => correspondenceLeftPulledInclusion f g h δ
local notation "π" => pullback.snd (pullback.snd f g) (pullback.fst g h)

/-- Forgetting the redundant middle coordinate identifies the full pulled graph
with the actual source-target ambient. -/
theorem isIso_leftGraphPulled_outerProjection :
    IsIso (iL ≫ correspondenceTripleOuterProjection f g h) := by
  have := isIso_integralGraph_sourceProjection f g φ hφ s
  have H := (isPullback_correspondenceLeftPulled f g h δ).paste_horiz
    (correspondenceTripleOuterProjection_isPullback f g h)
  exact H.isIso_fst_of_isIso

/-- The full graph pullback is the original outer ambient, without reduction. -/
def leftGraphPulledOuterIso : L ≅ pullback f h := by
  have := isIso_leftGraphPulled_outerProjection f g h φ hφ s
  exact asIso (iL ≫ correspondenceTripleOuterProjection f g h)

/-- The actual graph-pullback isomorphism preserves the endpoint ambient map. -/
theorem leftGraphPulledOuterIso_ambient :
    (leftGraphPulledOuterIso f g h φ hφ s).hom ≫
      correspondenceGraphFiberAmbientMap f g h φ hφ = iL ≫ π := by
  apply pullback.hom_ext
  · change (iL ≫ correspondenceTripleOuterProjection f g h) ≫
        correspondenceGraphFiberAmbientMap f g h φ hφ ≫ pullback.fst g h = _
    simp only [correspondenceGraphFiberAmbientMap, Category.assoc,
      pullback.map_fst, correspondenceTripleOuterProjection_fst_assoc]
    rw [← Category.assoc iL, (isPullback_correspondenceLeftPulled f g h δ).w]
    simp only [Category.assoc]
    rw [← integralComponentAt_graphMap_snd f g φ hφ s.val]
    exact (isPullback_correspondenceLeftPulledProjection f g h δ).w
  · simp [leftGraphPulledOuterIso, correspondenceGraphFiberAmbientMap,
      correspondenceTripleOuterProjection, correspondenceTripleTarget, pullback.map]

/-- A closed graph map gives a closed left support over the original right
ambient; it does not assert flatness of either correspondence support. -/
theorem leftGraphPulled_rightProjection_closed [IsClosedImmersion φ] :
    IsClosedImmersion (iL ≫ π) := by
  have := isIso_integralGraph_sourceProjection f g φ hφ s
  have : IsClosedImmersion ((integralComponentAt δ).subschemeι ≫ pullback.snd f g) := by
    rw [integralComponentAt_graphMap_snd, ← Category.assoc]
    infer_instance
  exact MorphismProperty.of_isPullback
    (isPullback_correspondenceLeftPulledProjection f g h δ) inferInstance

/-- The actual point transport from the triple ambient to the endpoint ambient. -/
theorem leftGraphPulledOuterIso_point (x : correspondenceTripleProduct f g h) (l : L)
    (hx : x = iL l) :
    π x = correspondenceGraphFiberAmbientMap f g h φ hφ
      ((leftGraphPulledOuterIso f g h φ hφ s).hom l) := by
  rw [hx]
  exact (congrArg (fun m => m l)
    (leftGraphPulledOuterIso_ambient f g h φ hφ s)).symm

/-- The literal original endpoint ambient stalk with its adjacent-ambient action. -/
abbrev leftGraphEndpointStalkModule (x : correspondenceTripleProduct f g h) (l : L)
    (hx : x = iL l) : ModuleCat ((pullback g h).presheaf.stalk (π x)) :=
  (ModuleCat.restrictScalars
    (((pullback g h).presheaf.stalkCongr
      (.of_eq (leftGraphPulledOuterIso_point f g h φ hφ s x l hx))).hom ≫
      (correspondenceGraphFiberAmbientMap f g h φ hφ).stalkMap
        ((leftGraphPulledOuterIso f g h φ hφ s).hom l)).hom).obj
    (ModuleCat.of
      ((pullback f h).presheaf.stalk ((leftGraphPulledOuterIso f g h φ hφ s).hom l))
      ((pullback f h).presheaf.stalk ((leftGraphPulledOuterIso f g h φ hφ s).hom l)))

/-- The full left graph stalk is the literal endpoint ambient stalk, with the
actual action from the adjacent ambient. No reduction or flatness is used. -/
def leftGraphPulledStalkIso (x : correspondenceTripleProduct f g h) (l : L)
    (hx : x = iL l) :
    leftGraphEndpointStalkModule f g h φ hφ s x l hx ≅
    (ModuleCat.restrictScalars ((π).stalkMap x).hom).obj
      ((ModuleCat.restrictScalars
        (((correspondenceTripleProduct f g h).presheaf.stalkCongr (.of_eq hx)).hom ≫
          (iL).stalkMap l).hom).obj
        (ModuleCat.of ((L).presheaf.stalk l) ((L).presheaf.stalk l))) :=
  Scheme.stalkModuleIsoOfOpenSquare
    (correspondenceGraphFiberAmbientMap f g h φ hφ) iL π
    (leftGraphPulledOuterIso f g h φ hφ s).hom
    (leftGraphPulledOuterIso_ambient f g h φ hφ s) x l hx
    (leftGraphPulledOuterIso_point f g h φ hφ s x l hx)

variable (w : pullback (C := Scheme) g h)

omit [IsIntegral X] [IsSeparated g] in
/-- The original support point has the actual adjacent-ambient image. -/
theorem graphIncidence_right_point (t : correspondenceIncidence f g h δ w) :
    π (correspondenceIncidenceInclusion f g h δ w t) =
      (integralComponentAt w).subschemeι (pullback.snd (C := Scheme) _ _ t) :=
  congrArg (fun m : correspondenceIncidence f g h δ w ⟶ pullback g h => m t)
    (correspondenceIncidenceInclusion_snd f g h δ w)

/-- The original right support stalk retains its full local scheme structure. -/
abbrev graphIncidenceOriginalSupportStalkModule (t : correspondenceIncidence f g h δ w) :
    ModuleCat ((pullback g h).presheaf.stalk (π (correspondenceIncidenceInclusion f g h δ w t))) :=
  (ModuleCat.restrictScalars
    (((pullback g h).presheaf.stalkCongr
      (.of_eq (graphIncidence_right_point f g h φ hφ s w t))).hom ≫
      (integralComponentAt w).subschemeι.stalkMap (pullback.snd (C := Scheme) _ _ t)).hom).obj
    (ModuleCat.of
      ((integralComponentAt w).subscheme.presheaf.stalk (pullback.snd (C := Scheme) _ _ t))
      ((integralComponentAt w).subscheme.presheaf.stalk (pullback.snd (C := Scheme) _ _ t)))

/-- All Tor lengths of the original pulled graph and support equal those of the
literal endpoint ambient and the original support. Only the ambient projection
is flat; the support may fail to be flat and its fiber may be nonreduced. -/
theorem graphPulledStalkTor_length_eq_endpointStalkTor [Flat f] [IsClosedImmersion φ]
    (t : correspondenceIncidence f g h δ w) (n : ℕ) :
    Module.length ((correspondenceTripleProduct f g h).presheaf.stalk
      (correspondenceIncidenceInclusion f g h δ w t))
      (((Tor (ModuleCat ((correspondenceTripleProduct f g h).presheaf.stalk
        (correspondenceIncidenceInclusion f g h δ w t))) n).obj
        (correspondenceIncidenceLeftPulledStalkModule f g h δ w t)).obj
        (correspondenceIncidenceRightPulledStalkModule f g h δ w t)) =
    Module.length ((pullback g h).presheaf.stalk
      (π (correspondenceIncidenceInclusion f g h δ w t)))
      (((Tor (ModuleCat ((pullback g h).presheaf.stalk
        (π (correspondenceIncidenceInclusion f g h δ w t)))) n).obj
        (leftGraphEndpointStalkModule f g h φ hφ s
          (correspondenceIncidenceInclusion f g h δ w t)
          (correspondenceIncidenceToLeftPulled f g h δ w t)
          (correspondenceIncidence_leftPulled_point_eq f g h δ w t))).obj
        (graphIncidenceOriginalSupportStalkModule f g h φ hφ s w t)) := by
  have := leftGraphPulled_rightProjection_closed f g h φ hφ s
  have hchange := Scheme.Hom.comapStalkTor_length_of_flat π (integralComponentAt w)
    (correspondenceIncidenceInclusion f g h δ w t)
    (correspondenceIncidenceToRightPulled f g h δ w t) (pullback.snd (C := Scheme) _ _ t)
    (correspondenceIncidence_rightPulled_point_eq f g h δ w t)
    (graphIncidence_right_point f g h φ hφ s w t) iL
    (correspondenceIncidenceToLeftPulled f g h δ w t)
    (correspondenceIncidence_leftPulled_point_eq f g h δ w t)
    (correspondenceIncidenceLeftPulledStalkModule f g h δ w t) n
  refine hchange.trans ?_
  exact (Functor.mapIso (Tor (ModuleCat ((pullback g h).presheaf.stalk
    (π (correspondenceIncidenceInclusion f g h δ w t)))) n)
    (leftGraphPulledStalkIso f g h φ hφ s
      (correspondenceIncidenceInclusion f g h δ w t)
      (correspondenceIncidenceToLeftPulled f g h δ w t)
      (correspondenceIncidence_leftPulled_point_eq f g h δ w t)).symm).app
        (graphIncidenceOriginalSupportStalkModule f g h φ hφ s w t) |>.toLinearEquiv.length_eq

end Stacks.Chow

namespace Stacks.Chow

variable (k : Type u) [Field k] {X Y Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))
    [IsIntegral X] [IsSeparated g] (φ : X ⟶ Y) (hφ : φ ≫ g = f)
    (s : genericPoints X) (w : pullback (C := Scheme) g h)

local notation "δ" => correspondenceGraphMap f g φ hφ s.val

/-- The native original graph-incidence Tor, in its actual four-factor ambient,
has exactly the full length of the literal endpoint-ambient stalk against the
original support stalk in every degree. This comparison precedes, and does not
replace, either finite-pushforward residue-degree factor or any image collision. -/
@[colib_tag "COL-1049"]
theorem graphIncidenceTor_length_eq_endpointStalkTor [Flat f] [IsClosedImmersion φ]
    (t : correspondenceIncidence f g h δ w) (n : ℕ) :
    Module.length ((correspondenceIntersectionAmbient f g h).presheaf.stalk
      (correspondenceIncidenceAmbientInclusion f g h δ w t))
      (((Tor (ModuleCat ((correspondenceIntersectionAmbient f g h).presheaf.stalk
        (correspondenceIncidenceAmbientInclusion f g h δ w t))) n).obj
        (correspondenceIncidenceSupportStalkModule f g h δ w t)).obj
        (correspondenceIncidenceTripleStalkModule f g h δ w t)) =
    Module.length ((pullback g h).presheaf.stalk
      (pullback.snd (pullback.snd f g) (pullback.fst g h)
        (correspondenceIncidenceInclusion f g h δ w t)))
      (((Tor (ModuleCat ((pullback g h).presheaf.stalk
        (pullback.snd (pullback.snd f g) (pullback.fst g h)
          (correspondenceIncidenceInclusion f g h δ w t)))) n).obj
        (leftGraphEndpointStalkModule f g h φ hφ s
          (correspondenceIncidenceInclusion f g h δ w t)
          (correspondenceIncidenceToLeftPulled f g h δ w t)
          (correspondenceIncidence_leftPulled_point_eq f g h δ w t))).obj
        (graphIncidenceOriginalSupportStalkModule f g h φ hφ s w t)) :=
  (incidenceTor_length_eq_pulledStalkTor k f g h δ w t n).trans
    (graphPulledStalkTor_length_eq_endpointStalkTor f g h φ hφ s w t n)

end Stacks.Chow
