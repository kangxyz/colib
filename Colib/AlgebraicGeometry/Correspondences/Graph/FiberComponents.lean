/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.ClopenFundamental
public import Colib.AlgebraicGeometry.Correspondences.Graph.LeftProjectedEndpoint

/-!
# All actual graph components cover the full support fiber

The genuine incidence with a graph component maps to the entire support fiber
by the actual source projection and the unchanged second projection. This map
is the base change of the graph component's source projection, so it is both
open and closed on a normal locally Noetherian source. These maps form a
finite disjoint cover. The full fundamental cycles, including nilpotents, add
to the fundamental cycle of the entire fiber.

No global integrality or nonemptiness is used. This extends the geometric
part of Graph.FlatFiber beyond its integral-source specialization, while
retaining the same native incidence and whole-fiber constructions.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped BigOperators

universe u

namespace Stacks.Chow

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
  (φ : X ⟶ Y) (hφ : φ ≫ g = f) [IsSeparated g]
  (w : pullback (C := Scheme) g h) (s : X)

/-- The original incidence maps to the full fiber, using the actual graph source map. -/
def correspondenceLeftGraphFiberMap :
    correspondenceIncidence f g h (correspondenceGraphMap f g φ hφ s) w ⟶
      correspondenceGraphFiber g h w φ :=
  pullback.map _ _ _ _
    ((integralComponentAt (correspondenceGraphMap f g φ hφ s)).subschemeι ≫
      pullback.fst f g) (𝟙 _) (𝟙 Y)
    (by simpa only [Category.comp_id, Category.assoc] using
      integralComponentAt_graphMap_snd f g φ hφ s) (by simp)

@[reassoc (attr := simp)] theorem correspondenceLeftGraphFiberMap_fst :
    correspondenceLeftGraphFiberMap f g h φ hφ w s ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫
        (integralComponentAt (correspondenceGraphMap f g φ hφ s)).subschemeι ≫
          pullback.fst f g := by
  simp [correspondenceLeftGraphFiberMap, pullback.map]

@[reassoc (attr := simp)] theorem correspondenceLeftGraphFiberMap_snd :
    correspondenceLeftGraphFiberMap f g h φ hφ w s ≫ pullback.snd _ _ =
      pullback.snd _ _ := by
  simp [correspondenceLeftGraphFiberMap, pullback.map]

/-- The map is precisely the base change of the graph component source projection. -/
theorem isPullback_correspondenceLeftGraphFiberMap :
    IsPullback (correspondenceLeftGraphFiberMap f g h φ hφ w s)
      (pullback.fst _ _) (pullback.fst _ _)
      ((integralComponentAt (correspondenceGraphMap f g φ hφ s)).subschemeι ≫
        pullback.fst f g) := by
  have H : IsPullback
      (correspondenceLeftGraphFiberMap f g h φ hφ w s ≫ pullback.snd _ _)
      (pullback.fst _ _) ((integralComponentAt w).subschemeι ≫ pullback.fst g h)
      (((integralComponentAt (correspondenceGraphMap f g φ hφ s)).subschemeι ≫
        pullback.fst f g) ≫ φ) := by
    simpa only [correspondenceLeftGraphFiberMap_snd, Category.assoc,
      integralComponentAt_graphMap_snd] using
        (IsPullback.of_hasPullback
          ((integralComponentAt (correspondenceGraphMap f g φ hφ s)).subschemeι ≫
            pullback.snd f g)
          ((integralComponentAt w).subschemeι ≫ pullback.fst g h)).flip
  exact H.of_right (by simp)
    (IsPullback.of_hasPullback φ
      ((integralComponentAt w).subschemeι ≫ pullback.fst g h)).flip

instance correspondenceLeftGraphFiberMap_isClosedImmersion :
    IsClosedImmersion (correspondenceLeftGraphFiberMap f g h φ hφ w s) := by
  have := isClosedImmersion_integralComponentAt_graphMap_fst f g φ hφ s
  exact MorphismProperty.of_isPullback
    (isPullback_correspondenceLeftGraphFiberMap f g h φ hφ w s).flip inferInstance

/-- Its actual image is exactly the source-component part of the full fiber. -/
theorem range_correspondenceLeftGraphFiberMap :
    Set.range (correspondenceLeftGraphFiberMap f g h φ hφ w s) =
      (pullback.fst φ ((integralComponentAt w).subschemeι ≫ pullback.fst g h)) ⁻¹'
        closure ({s} : Set X) := by
  let a := pullback.fst φ ((integralComponentAt w).subschemeι ≫ pullback.fst g h)
  let b := (integralComponentAt (correspondenceGraphMap f g φ hφ s)).subschemeι ≫ pullback.fst f g
  have H : IsPullback (correspondenceLeftGraphFiberMap f g h φ hφ w s) _ a b :=
    isPullback_correspondenceLeftGraphFiberMap f g h φ hφ w s
  rw [← H.isoPullback_hom_fst]
  change Set.range (⇑(pullback.fst (C := Scheme) a b) ∘ ⇑H.isoPullback.hom) = _
  rw [Set.range_comp, Set.range_eq_univ.mpr H.isoPullback.hom.surjective, Set.image_univ,
    Scheme.Pullback.range_fst, range_integralComponentAt_graphMap_fst]

/-- The actual map to the outer product is unchanged. -/
@[reassoc (attr := simp)] theorem correspondenceLeftGraphFiberMap_outer :
    correspondenceLeftGraphFiberMap f g h φ hφ w s ≫
      correspondenceGraphFiberMap f g h w φ hφ =
        correspondenceIncidenceMap f g h (correspondenceGraphMap f g φ hφ s) w := by
  apply pullback.hom_ext
  · simp [correspondenceIncidenceLeft]
  · simp [correspondenceIncidenceRight]

variable [IsLocallyNoetherian X] [IsNormal X]

/-- On a normal source the same actual fiber map is open. -/
theorem isOpenImmersion_correspondenceLeftGraphFiberMap (s : genericPoints X) :
    IsOpenImmersion (correspondenceLeftGraphFiberMap f g h φ hφ w s.val) := by
  have := isOpenImmersion_integralComponentAt_graphMap_fst f g φ hφ s
  exact MorphismProperty.of_isPullback
    (isPullback_correspondenceLeftGraphFiberMap f g h φ hφ w s.val).flip inferInstance

/-- Every point of the full fiber lies in exactly one actual graph-component piece. -/
theorem existsUnique_correspondenceLeftGraphFiberMap
    (x : correspondenceGraphFiber g h w φ) :
    ∃! s : genericPoints X,
      x ∈ Set.range (correspondenceLeftGraphFiberMap f g h φ hφ w s.val) := by
  let y := pullback.fst φ ((integralComponentAt w).subschemeι ≫ pullback.fst g h) x
  let C : irreducibleComponents X :=
    ⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y⟩
  let s : genericPoints X := genericPoints.ofComponent C
  have hs : y ∈ closure ({s.val} : Set X) := by
    have he : closure ({s.val} : Set X) = C.val := genericPoints.isGenericPoint_ofComponent C
    rw [he]
    exact mem_irreducibleComponent
  refine ⟨s, ?_, ?_⟩
  · change x ∈ Set.range (correspondenceLeftGraphFiberMap f g h φ hφ w s.val)
    rw [range_correspondenceLeftGraphFiberMap]
    exact hs
  · intro t ht
    rw [range_correspondenceLeftGraphFiberMap] at ht
    by_contra hts
    have hne : closure ({t.val} : Set X) ≠ closure ({s.val} : Set X) := fun he =>
      hts (genericPoints.component_injective (Subtype.ext he))
    have hd := disjoint_of_mem_irreducibleComponents_of_isNormal
      (closure ({t.val} : Set X)) (closure ({s.val} : Set X)) t.property s.property hne
    exact Set.disjoint_left.mp hd ht hs

/-- The actual graph component incidences add to the full unreduced fiber cycle. -/
theorem fundamentalCycle_graphFiber_eq_sum_incidence
    [Fintype (genericPoints X)] [IsNoetherian (correspondenceGraphFiber g h w φ)]
    [∀ s : genericPoints X, IsNoetherian
      (correspondenceIncidence f g h (correspondenceGraphMap f g φ hφ s.val) w)] :
    AlgebraicCycle.fundamentalCycle (correspondenceGraphFiber g h w φ) =
      ∑ s : genericPoints X,
        finiteCyclePushforward (correspondenceLeftGraphFiberMap f g h φ hφ w s.val)
          (AlgebraicCycle.fundamentalCycle
            (correspondenceIncidence f g h (correspondenceGraphMap f g φ hφ s.val) w)) := by
  have : ∀ s : genericPoints X,
      IsOpenImmersion (correspondenceLeftGraphFiberMap f g h φ hφ w s.val) :=
    fun s => isOpenImmersion_correspondenceLeftGraphFiberMap f g h φ hφ w s
  exact fundamentalCycle_eq_sum_clopen
    (fun s : genericPoints X =>
      correspondenceIncidence f g h (correspondenceGraphMap f g φ hφ s.val) w)
    (fun s => correspondenceLeftGraphFiberMap f g h φ hφ w s.val)
    (existsUnique_correspondenceLeftGraphFiberMap f g h φ hφ w)

end Stacks.Chow
