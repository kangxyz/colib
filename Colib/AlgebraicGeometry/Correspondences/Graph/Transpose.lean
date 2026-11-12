/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.IntegralFundamental
public import Colib.AlgebraicGeometry.Correspondences.Graph.TargetPushforward

/-!
# Finite flat transposed graphs and their actual graph composite

For a finite flat morphism between the original smooth-site objects, the transposed graph is
the pushforward of the whole source fundamental cycle along the literal map `(q, id)`.
Admissibility uses flatness of the whole source projection, not of reduced components.
Its composite with the original graph is the diagonal pushforward of the original fundamental
cycle pushed along `q`. On integral objects this is the actual generic residue degree times
the categorical identity. No separability hypothesis or degree-one replacement is used.

This is only the transpose-then-graph identity. The opposite composite for a radicial map
requires a separate calculation of the nonreduced self-fiber product. Neither that calculation
nor purely inseparable field-change invariance is asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow
open Function.locallyFinsuppWithin

attribute [local instance] Classical.propDecidable

universe u

namespace AlgebraicGeometry.Cor

variable (k : Type u) [Field k]

local instance smoothSiteNoetherian (X : Scheme.SmoothSite (Spec (.of k))) :
    IsNoetherian X.left :=
  { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (Y := Spec (.of k)) X.hom
    toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (Y := Spec (.of k)) X.hom }

local instance smoothSiteReduced (X : Scheme.SmoothSite (Spec (.of k))) :
    IsReduced X.left := isReduced_of_smooth (Y := Spec (.of k)) X.hom

variable {X Y : Scheme.SmoothSite (Spec (.of k))} (q : X ⟶ Y)

/-- The literal reversed graph, with first coordinate `q` and second coordinate the identity. -/
def transposeGraphMap : X.left ⟶ pullback Y.hom X.hom :=
  pullback.lift q.left (𝟙 X.left) (by simp)

@[reassoc (attr := simp)]
theorem transposeGraphMap_fst :
    transposeGraphMap k q ≫ pullback.fst Y.hom X.hom = q.left := by
  simp [transposeGraphMap]

@[reassoc (attr := simp)]
theorem transposeGraphMap_snd :
    transposeGraphMap k q ≫ pullback.snd Y.hom X.hom = 𝟙 X.left := by
  simp [transposeGraphMap]

instance transposeGraphMap_isClosedImmersion : IsClosedImmersion (transposeGraphMap k q) := by
  have : IsClosedImmersion (transposeGraphMap k q ≫ pullback.snd Y.hom X.hom) := by
    rw [transposeGraphMap_snd]
    infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.snd Y.hom X.hom)

local instance transposeGraphMap_fst_finite [IsFinite q.left] :
    IsFinite (transposeGraphMap k q ≫ pullback.fst Y.hom X.hom) := by
  rw [transposeGraphMap_fst]
  infer_instance

local instance transposeGraphMap_fst_flat [Flat q.left] :
    Flat (transposeGraphMap k q ≫ pullback.fst Y.hom X.hom) := by
  rw [transposeGraphMap_fst]
  infer_instance

/-- The transposed graph is an actual native finite correspondence, with its full cycle. -/
@[colib_tag "COL-1088", colib_ref "MVW2006"
  "Lecture 1, transpose paragraph and Construction 1.3, printed p. 4"
  "adaptation" "finite flat transposed graphs on original smooth-site objects with full cycles"]
def finiteFlatTranspose [IsFinite q.left] [Flat q.left] : Cor.mk Y ⟶ Cor.mk X :=
  finiteFlatSpanFundamental Y.hom X.hom (transposeGraphMap k q)

@[simp]
theorem finiteFlatTranspose_val [IsFinite q.left] [Flat q.left] :
    (finiteFlatTranspose k q).val =
      finiteCyclePushforward (transposeGraphMap k q) (AlgebraicCycle.fundamentalCycle X.left) :=
  rfl

/-- Every original generic length and residue degree occurs in the actual transpose cycle. -/
theorem finiteFlatTranspose_val_apply [IsFinite q.left] [Flat q.left]
    (z : (pullback Y.hom X.hom : Scheme.{u})) :
    (finiteFlatTranspose k q).val z =
      letI := (AlgebraicCycle.fundamentalCycle_genericPoints_finite X.left).fintype
      ∑ x : genericPoints X.left,
        if z = transposeGraphMap k q x.val then
          ((Module.length (X.left.presheaf.stalk x.val)
            (X.left.presheaf.stalk x.val)).toNat : ℤ) *
              ((transposeGraphMap k q).residueDegree x.val : ℤ)
        else 0 := by
  exact finiteCyclePushforward_ofGenericCoefficients_apply _ _ _ z

local instance graphTargetMap_finite [IsFinite q.left]
    (T : Scheme.SmoothSite (Spec (.of k))) : IsFinite (graphTargetMap k T q) := by
  change IsFinite (pullback.map T.hom X.hom T.hom Y.hom
    (𝟙 T.left) q.left (𝟙 _) (by simp) (by simp))
  exact MorphismProperty.pullbackMap (P := @AlgebraicGeometry.IsFinite)
    (inferInstance : IsFinite (𝟙 T.left)) (inferInstance : IsFinite q.left)
    (by simp) (MorphismProperty.Over.w q).symm

local instance diagonalGraph_closed (T : Scheme.SmoothSite (Spec (.of k))) :
    IsClosedImmersion (correspondenceGraphMap T.hom T.hom (𝟙 T.left) (Category.id_comp _)) :=
  isClosedImmersion_correspondenceGraphMap T.hom T.hom (𝟙 T.left) (Category.id_comp _)

/-- The original graph composite keeps the entire source cycle and the actual finite map. -/
@[colib_tag "COL-1088", colib_ref "MVW2006"
  "Lecture 1, pushforward and composition, printed pp. 4-5"
  "adaptation" "transpose-then-graph is the diagonal pushforward of the original full cycle"]
theorem finiteFlatTranspose_comp_graph_val [IsFinite q.left] [Flat q.left] :
    (finiteFlatTranspose k q ≫ (graphFunctor k).map q).val =
      finiteCyclePushforward
        (correspondenceGraphMap Y.hom Y.hom (𝟙 Y.left) (Category.id_comp _))
        (finiteCyclePushforward q.left (AlgebraicCycle.fundamentalCycle X.left)) := by
  refine (comp_graph_val_of_finite k q (finiteFlatTranspose k q)).trans ?_
  change finiteCyclePushforward (graphTargetMap k Y q)
      (finiteCyclePushforward (transposeGraphMap k q)
        (AlgebraicCycle.fundamentalCycle X.left)) = _
  have hmap : transposeGraphMap k q ≫ graphTargetMap k Y q =
      q.left ≫ correspondenceGraphMap Y.hom Y.hom (𝟙 Y.left) (Category.id_comp _) := by
    apply pullback.hom_ext <;> simp
  rw [finiteCyclePushforward_comp_apply, finiteCyclePushforward_comp_apply]
  simp only [hmap]

/-- On integral objects the literal composite is the actual generic residue degree times
the categorical identity. Inseparable degrees are retained. -/
@[colib_tag "COL-1088", colib_ref "MVW2006"
  "Lecture 1, Exercise 1.11, printed p. 6"
  "adaptation" "generic degree formula for finite flat maps of integral smooth-site objects"]
theorem finiteFlatTranspose_comp_graph_of_isIntegral
    [IsIntegral X.left] [IsIntegral Y.left] [IsFinite q.left] [Flat q.left] :
    finiteFlatTranspose k q ≫ (graphFunctor k).map q =
      (q.left.residueDegree (genericPoint X.left) : ℤ) • 𝟙 (Cor.mk Y) := by
  have hgeneric : q.left (genericPoint X.left) = genericPoint Y.left := by
    have h := mem_genericPoints_of_flat q.left (genericPoint_mem_genericPoints X.left)
    simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using h
  have hpush : finiteCyclePushforward q.left (AlgebraicCycle.fundamentalCycle X.left) =
      (q.left.residueDegree (genericPoint X.left) : ℤ) •
        AlgebraicCycle.fundamentalCycle Y.left := by
    rw [AlgebraicCycle.fundamentalCycle_eq_single_genericPoint,
      AlgebraicCycle.fundamentalCycle_eq_single_genericPoint,
      finiteCyclePushforward_single, hgeneric, one_mul]
    ext z
    by_cases hz : z = genericPoint Y.left <;> simp [single_apply, hz]
  have hid : finiteCyclePushforward
      (correspondenceGraphMap Y.hom Y.hom (𝟙 Y.left) (Category.id_comp _))
      (AlgebraicCycle.fundamentalCycle Y.left) =
        (𝟙 (Cor.mk Y) : finiteCorrespondences Y.hom Y.hom).val :=
    finiteCyclePushforward_fundamentalCycle_graph (X := Y.left) (Y := Y.left)
      Y.hom Y.hom (𝟙 Y.left) (Category.id_comp _)
  apply Subtype.ext
  refine (finiteFlatTranspose_comp_graph_val k q).trans ?_
  change finiteCyclePushforward
      (correspondenceGraphMap Y.hom Y.hom (𝟙 Y.left) (Category.id_comp _))
      (finiteCyclePushforward q.left (AlgebraicCycle.fundamentalCycle X.left)) =
    (q.left.residueDegree (genericPoint X.left) : ℤ) •
      (𝟙 (Cor.mk Y) : finiteCorrespondences Y.hom Y.hom).val
  rw [hpush, map_zsmul, hid]

end AlgebraicGeometry.Cor
