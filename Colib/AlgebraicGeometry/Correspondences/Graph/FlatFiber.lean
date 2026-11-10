/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.FlatSourceCycle
public import Colib.AlgebraicGeometry.Correspondences.Graph.PrecompositionSum

/-!
# Actual left-graph composition and the whole finite-flat support fiber

On an integral source there is one actual graph component. Its source
projection is an isomorphism, so the actual incidence is the entire pullback
of the second support. The constructed isomorphism preserves both projections
and the actual outer map. Flatness of the second source projection, not of
the morphism whose graph is used, gives the fundamental-cycle formula.

The result keeps all nonreduced fiber lengths and the original integer cycle.
This is a source-only native reconstruction of motivic
Graph/Flat/LeftComposition.lean:222-349 at a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped BigOperators

universe u

namespace Stacks.Chow

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
  (w : pullback (C := Scheme) g h) (φ : X ⟶ Y) (hφ : φ ≫ g = f)

/-- The whole scheme-theoretic support fiber, without reduction. -/
abbrev correspondenceGraphFiber : Scheme.{u} :=
  pullback φ ((integralComponentAt w).subschemeι ≫ pullback.fst g h)

/-- Its outer map has the original source and final support coordinate. -/
def correspondenceGraphFiberMap : correspondenceGraphFiber g h w φ ⟶ pullback f h :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ (integralComponentAt w).subschemeι ≫ pullback.snd g h) (by
      rw [← hφ, ← Category.assoc, pullback.condition]
      simp only [Category.assoc]
      rw [pullback.condition])

@[reassoc (attr := simp)] theorem correspondenceGraphFiberMap_fst :
    correspondenceGraphFiberMap f g h w φ hφ ≫ pullback.fst f h = pullback.fst _ _ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem correspondenceGraphFiberMap_snd :
    correspondenceGraphFiberMap f g h w φ hφ ≫ pullback.snd f h =
      pullback.snd _ _ ≫ (integralComponentAt w).subschemeι ≫ pullback.snd g h :=
  pullback.lift_snd _ _ _

/-- The unchanged final factor and the original source map induce the ambient map. -/
def correspondenceGraphFiberAmbientMap : pullback f h ⟶ pullback g h :=
  pullback.map f h g h φ (𝟙 Z) (𝟙 S) (by simpa using hφ.symm) (by simp)

/-- The whole fiber is the actual inverse image of the original closed support. -/
theorem isPullback_correspondenceGraphFiberMap :
    IsPullback (correspondenceGraphFiberMap f g h w φ hφ) (pullback.snd _ _)
      (correspondenceGraphFiberAmbientMap f g h φ hφ) (integralComponentAt w).subschemeι where
  w := by
    apply pullback.hom_ext
    · simpa [correspondenceGraphFiberAmbientMap, pullback.map, Category.assoc] using
        (pullback.condition
          (f := φ) (g := (integralComponentAt w).subschemeι ≫ pullback.fst g h))
    · simp [correspondenceGraphFiberAmbientMap, pullback.map]
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun c => by
    have hf := congrArg (fun m => m ≫ pullback.fst g h) c.condition
    have hs := congrArg (fun m => m ≫ pullback.snd g h) c.condition
    simp only [Category.assoc, correspondenceGraphFiberAmbientMap, pullback.map,
      pullback.lift_fst, pullback.lift_snd, Category.comp_id] at hf hs
    let m := pullback.lift (c.fst ≫ pullback.fst f h) c.snd
      (by simpa only [Category.assoc] using hf)
    have hm : m ≫ correspondenceGraphFiberMap f g h w φ hφ = c.fst := by
      apply pullback.hom_ext
      · simp [m]
      · simpa [m] using hs.symm
    refine ⟨m, hm, pullback.lift_snd _ _ _, ?_⟩
    intro n hn hn'
    apply pullback.hom_ext (f := φ)
      (g := (integralComponentAt w).subschemeι ≫ pullback.fst g h) (k := n) (l := m)
    · simpa [m] using congrArg (fun q => q ≫ pullback.fst f h) hn
    · simpa [m] using hn')⟩

/-- The outer fiber map is a closed immersion, so no hidden residue-degree factor occurs. -/
instance correspondenceGraphFiberMap_isClosedImmersion :
    IsClosedImmersion (correspondenceGraphFiberMap f g h w φ hφ) :=
  MorphismProperty.of_isPullback
    (isPullback_correspondenceGraphFiberMap f g h w φ hφ).flip inferInstance

/-- Every point of the whole support fiber has literal residue degree one into the ambient. -/
theorem correspondenceGraphFiberMap_residueDegree (x : correspondenceGraphFiber g h w φ) :
    (correspondenceGraphFiberMap f g h w φ hφ).residueDegree x = 1 :=
  residueDegree_eq_one_of_isPreimmersion _ _

/-- The actual whole fiber map is finite by the second support's finiteness. -/
theorem isFinite_correspondenceGraphFiberMap [IsSeparated h]
    (hw : IsFiniteCorrespondencePoint g h w) :
    IsFinite (correspondenceGraphFiberMap f g h w φ hφ) := by
  have : IsFinite ((integralComponentAt w).subschemeι ≫ pullback.fst g h) := hw.1
  have : IsFinite (correspondenceGraphFiberMap f g h w φ hφ ≫ pullback.fst f h) := by
    rw [correspondenceGraphFiberMap_fst]
    infer_instance
  exact IsFinite.of_comp _ (pullback.fst f h)

/-- The full fiber of a finite support over a Noetherian source is Noetherian. -/
theorem isNoetherian_correspondenceGraphFiber [IsNoetherian X]
    (hw : IsFiniteCorrespondencePoint g h w) :
    IsNoetherian (correspondenceGraphFiber g h w φ) := by
  have : IsFinite ((integralComponentAt w).subschemeι ≫ pullback.fst g h) := hw.1
  exact
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (pullback.fst _ _)
      toCompactSpace := inferInstance }

section IntegralGraph

variable [IsIntegral X] [IsSeparated g] (s : genericPoints X)

local notation "δ" => correspondenceGraphMap f g φ hφ s.val

/-- The unique integral-source graph component projects isomorphically to that source. -/
theorem isIso_integralGraph_sourceProjection :
    IsIso ((integralComponentAt δ).subschemeι ≫ pullback.fst f g) := by
  have := isClosedImmersion_integralComponentAt_graphMap_fst f g φ hφ s.val
  have hs : closure ({s.val} : Set X) = Set.univ := by
    have := s.property
    simpa only [genericPoints, Set.mem_ofPred_eq, irreducibleComponents_eq_singleton,
      Set.mem_singleton_iff] using this
  have : Surjective ((integralComponentAt δ).subschemeι ≫ pullback.fst f g) :=
    ⟨Set.range_eq_univ.mp ((range_integralComponentAt_graphMap_fst f g φ hφ s.val).trans hs)⟩
  exact isIso_of_isClosedImmersion_of_surjective _

/-- The actual incidence is the whole support fiber, preserving nilpotents. -/
def correspondenceLeftGraphFiberIso :
    correspondenceIncidence f g h δ w ≅ correspondenceGraphFiber g h w φ := by
  letI := isIso_integralGraph_sourceProjection f g φ hφ s
  exact asIso (pullback.map _ _ _ _
    ((integralComponentAt δ).subschemeι ≫ pullback.fst f g) (𝟙 _) (𝟙 Y)
    (by simpa only [Category.comp_id, Category.assoc] using
      (integralComponentAt_graphMap_snd f g φ hφ s.val)) (by simp))

@[reassoc (attr := simp)] theorem correspondenceLeftGraphFiberIso_fst :
    (correspondenceLeftGraphFiberIso f g h w φ hφ s).hom ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ (integralComponentAt δ).subschemeι ≫ pullback.fst f g := by
  simp [correspondenceLeftGraphFiberIso, pullback.map]

@[reassoc (attr := simp)] theorem correspondenceLeftGraphFiberIso_snd :
    (correspondenceLeftGraphFiberIso f g h w φ hφ s).hom ≫ pullback.snd _ _ =
      pullback.snd _ _ := by
  simp [correspondenceLeftGraphFiberIso, pullback.map]

/-- The genuine native incidence outer map is exactly the whole fiber outer map. -/
theorem correspondenceLeftGraphFiberIso_map :
    (correspondenceLeftGraphFiberIso f g h w φ hφ s).hom ≫
      correspondenceGraphFiberMap f g h w φ hφ = correspondenceIncidenceMap f g h δ w := by
  apply pullback.hom_ext
  · simp [correspondenceIncidenceLeft]
  · simp [correspondenceIncidenceRight]

end IntegralGraph

end Stacks.Chow

namespace AlgebraicGeometry.Cor

open Stacks.Chow

variable (k : Type u) [Field k] {X Y Z : Scheme.SmoothSite (Spec (.of k))}
  [IsIntegral X.left]
  (w : pullback (C := Scheme) Y.hom Z.hom)
  (hw : IsFiniteCorrespondencePoint Y.hom Z.hom w)
  [Flat ((integralComponentAt w).subschemeι ≫ pullback.fst Y.hom Z.hom)]

/-- Actual graph precomposition is the whole fiber cycle with its true generic lengths. -/
theorem graph_comp_single_val_eq_fiber (φ : X ⟶ Y) :
    letI : IsNoetherian X.left :=
      { toIsLocallyNoetherian :=
          LocallyOfFiniteType.isLocallyNoetherian (Y := Spec (.of k)) X.hom
        toCompactSpace :=
          QuasiCompact.compactSpace_of_compactSpace (Y := Spec (.of k)) X.hom }
    letI := isFinite_correspondenceGraphFiberMap X.hom Y.hom Z.hom w φ.left
      (MorphismProperty.Over.w φ) hw
    letI := isNoetherian_correspondenceGraphFiber (X := X.left) Y.hom Z.hom w φ.left hw
    ((graphFunctor k).map φ ≫
      singleFiniteCorrespondence Y.hom Z.hom w hw 1).val =
      finiteCyclePushforward
        (correspondenceGraphFiberMap X.hom Y.hom Z.hom w φ.left (MorphismProperty.Over.w φ))
        (AlgebraicCycle.fundamentalCycle (correspondenceGraphFiber Y.hom Z.hom w φ.left)) := by
  classical
  have : IsNoetherian X.left :=
    { toIsLocallyNoetherian :=
        LocallyOfFiniteType.isLocallyNoetherian (Y := Spec (.of k)) X.hom
      toCompactSpace :=
        QuasiCompact.compactSpace_of_compactSpace (Y := Spec (.of k)) X.hom }
  have := isFinite_correspondenceGraphFiberMap X.hom Y.hom Z.hom w φ.left
    (MorphismProperty.Over.w φ) hw
  have := isNoetherian_correspondenceGraphFiber (X := X.left) Y.hom Z.hom w φ.left hw
  let := (finite_genericPoints k (Cor.mk X)).fintype
  let s : genericPoints X.left :=
    ⟨genericPoint X.left, by rw [genericPoints_eq_singleton]; exact Set.mem_singleton _⟩
  let : Unique (genericPoints X.left) :=
    { default := s
      uniq := fun t => Subtype.ext (by
        have ht := t.property
        simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using ht) }
  rw [graph_comp_single_eq_sum_incidence]
  rw [Fintype.sum_subsingleton _ s]
  simp only [one_smul]
  let δ := correspondenceGraphMap X.hom Y.hom φ.left (MorphismProperty.Over.w φ) s.val
  let hδ := isFiniteCorrespondencePoint_graphMap X.hom Y.hom φ.left
    (MorphismProperty.Over.w φ) s
  have := isNoetherian_correspondenceIncidence_of_finite_source
    (X := X.left) X.hom Y.hom Z.hom δ w hδ hw
  have := isFinite_correspondenceIncidenceMap X.hom Y.hom Z.hom δ w hδ hw
  rw [incidenceTorCorrespondence_val_of_flat_source]
  let e := correspondenceLeftGraphFiberIso (X := X.left) X.hom Y.hom Z.hom w φ.left
    (MorphismProperty.Over.w φ) s
  have hem : e.hom ≫
      correspondenceGraphFiberMap X.hom Y.hom Z.hom w φ.left (MorphismProperty.Over.w φ) =
        correspondenceIncidenceMap X.hom Y.hom Z.hom δ w :=
    correspondenceLeftGraphFiberIso_map (X := X.left) X.hom Y.hom Z.hom w φ.left
      (MorphismProperty.Over.w φ) s
  have he := finiteCyclePushforward_fundamentalCycle_iso
    (A := correspondenceIncidence X.hom Y.hom Z.hom δ w)
    (X := correspondenceGraphFiber Y.hom Z.hom w φ.left) e
  simpa only [he, hem] using
    (finiteCyclePushforward_comp_apply e.hom
      (correspondenceGraphFiberMap X.hom Y.hom Z.hom w φ.left (MorphismProperty.Over.w φ))
      (AlgebraicCycle.fundamentalCycle (correspondenceIncidence X.hom Y.hom Z.hom δ w))).symm

end AlgebraicGeometry.Cor
