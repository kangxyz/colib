/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassBottomCommonFamily
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH0ProjectionBoundaryRows
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH1MiddleJoin
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceProductColumns
public import Colib.Topology.Realization.SimplexProductGrid

/-!
# The actual shared center of the first H₁ face and the Laurent bottom

Both nodes retain their chosen original references after normalization.
Their equality is the actual anchored three-factor pullback coherence.
Adapted from `H1BottomCenter.lean` in the original BoundedFlat Bass proof at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open AlgebraicGeometry.Scheme.BaseChange.Coefficients CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1Join

open ModelSimplex BoundedFlatCoefficientBassH1References BoundedFlatPerfectReferenceCoherence

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The actual positive projection equation in the original first component's source. -/
theorem bottomSourceGeom :
    coefficientMap P ((laurentUnderFunctor R).map u) ≫ laurentProjection P a =
      coefficientMap P ((laurentUnderFunctor R).map u) ≫
        (laurentPlus P a ≫ polynomialProjection P a) :=
  congrArg (fun h ↦ coefficientMap P ((laurentUnderFunctor R).map u) ≫ h)
    (laurentPlus_projection P a).symm

/-- The first H1 center node formed from the Laurent binary target for `u`, then postcomposed by
the Laurent map for `v`. -/
def firstBottomCenter : BoundedFlatCoefficientBassOverlap.Node P u v :=
  postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassH1Components.laurentMap P v)
    (firstIso P u v)
    (⟨BoundedFlatPerfectBinarySimplex.targetMap
      (coefficientMap P ((laurentUnderFunctor R).map u))
      (laurentPlus P a ≫ polynomialProjection P a),
      eqToIso (BoundedFlatCoefficientBassH0ProjectionBoundaryRows.sourceAnchor P u
        (underToLaurent R)
        (laurentPlus_projection P a)) ≪≫ BoundedFlatPerfectBinarySimplex.total
        (coefficientMap P ((laurentUnderFunctor R).map u))
        (laurentPlus P a ≫ polynomialProjection P a)⟩ :
      BoundedFlatCoefficientBassH0Diagram.Node P u)

/-- The bottom target center node obtained by precomposing the Laurent binary target with the
projection source. -/
def bottomTargetCenter : BoundedFlatCoefficientBassOverlap.Node P u v :=
  preReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassProjectionPath.source P a)
    (BoundedFlatCoefficientBassBottomCommonFamily.referenceIso P u v)
    (⟨BoundedFlatPerfectBinarySimplex.targetMap
      (coefficientMap P ((laurentUnderFunctor R).map v))
      (coefficientMap P ((laurentUnderFunctor R).map u)),
      BoundedFlatPerfectBinarySimplex.total
        (coefficientMap P ((laurentUnderFunctor R).map v))
        (coefficientMap P ((laurentUnderFunctor R).map u))⟩ :
      Σ G,
        (BoundedFlatCoefficientBassLaurentBottomFace.source P u v).hom.toFunctor ≅ G.hom.toFunctor)

/-- The displayed reference is literally the original first-component center reference. -/
theorem first_bottom_center_original : BoundedFlatCoefficientBassH1References.firstNodes P u v 2 =
    firstBottomCenter P u v := rfl

/-- The bottom's actual final column retains the original Laurent normalization reference. -/
theorem bottom_target_center_original :
    BoundedFlatCoefficientBassBottomCommonFamily.bottomNodes P u v 2 =
      bottomTargetCenter P u v := by
  change BoundedFlatCoefficientBassBottomCommonFamily.bottomNodes P u v
    (Topology.SimplexGrid.index 4 2 (0, 2)) = _
  unfold BoundedFlatCoefficientBassBottomCommonFamily.bottomNodes CommonReferenceProduct.vertices
    CommonReferenceProduct.references
  rw [Topology.SimplexGrid.decode_index]
  dsimp only
  have hf : ((BoundedFlatCoefficientBassProjectionPath.nodes P a 0).1 ≫
      BoundedFlatCoefficientBassLaurentBottomFace.vertices P u v 2).hom.toFunctor =
      (bottomTargetCenter P u v).1.hom.toFunctor := rfl
  apply ModelSimplex.reference_node_eq hf
  simp only [eqToHom_refl, Category.comp_id]
  apply congrArg Iso.hom
  change BoundedFlatCoefficientBassBottomCommonFamily.referenceIso P u v ≪≫
    (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
      ((Iso.refl (BoundedFlatCoefficientBassProjectionPath.source P a).hom.toFunctor).prod
        (BoundedFlatPerfectBinarySimplex.total
          (coefficientMap P ((laurentUnderFunctor R).map v))
          (coefficientMap P ((laurentUnderFunctor R).map u)))) = _
  have hi := CommonReferenceProduct.composition_pair_iso
    (Iso.refl (BoundedFlatCoefficientBassProjectionPath.source P a).hom.toFunctor)
    (BoundedFlatPerfectBinarySimplex.total (coefficientMap P ((laurentUnderFunctor R).map v))
      (coefficientMap P ((laurentUnderFunctor R).map u)))
  simp only [isoWhiskerRight_refl, Iso.refl_trans] at hi
  exact congrArg
    (fun ν ↦ BoundedFlatCoefficientBassBottomCommonFamily.referenceIso P u v ≪≫ ν) hi

/-- The ordered three pullbacks give the same literally associated target functor. -/
theorem bottom_center_functor : (firstBottomCenter P u v).1.hom.toFunctor =
    (bottomTargetCenter P u v).1.hom.toFunctor := rfl

/-- The source/bottom common node keeps the actual projection and Laurent composition isos. -/
theorem bottom_center_reference : (firstBottomCenter P u v).2 =
    (bottomTargetCenter P u v).2 := by
  have he : eqToIso (BoundedFlatCoefficientBassH0ProjectionBoundaryRows.sourceAnchor P u
        (underToLaurent R)
      (laurentPlus_projection P a)) ≪≫ BoundedFlatPerfectBinarySimplex.total
      (coefficientMap P ((laurentUnderFunctor R).map u))
      (laurentPlus P a ≫ polynomialProjection P a) =
    smallIso (eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback (bottomSourceGeom P u)) ≪≫
      boundedAboveFlatPerfectNormalizedPullbackCompIso
        (coefficientMap P ((laurentUnderFunctor R).map u))
        (laurentPlus P a ≫ polynomialProjection P a)) := by
    rw [smallIso_trans, smallIso_eqToIso]
    rfl
  change firstIso P u v ≪≫ isoWhiskerRight
      (eqToIso (BoundedFlatCoefficientBassH0ProjectionBoundaryRows.sourceAnchor P u
        (underToLaurent R)
        (laurentPlus_projection P a)) ≪≫ BoundedFlatPerfectBinarySimplex.total
        (coefficientMap P ((laurentUnderFunctor R).map u))
        (laurentPlus P a ≫ polynomialProjection P a))
      (BoundedFlatCoefficientBassH1Components.laurentMap P v).hom.toFunctor =
    BoundedFlatCoefficientBassBottomCommonFamily.referenceIso P u v ≪≫
      isoWhiskerLeft (BoundedFlatCoefficientBassProjectionPath.source P a).hom.toFunctor
        (BoundedFlatPerfectBinarySimplex.total (coefficientMap P ((laurentUnderFunctor R).map v))
          (coefficientMap P ((laurentUnderFunctor R).map u)))
  rw [he]
  change smallIso (eqToIso
      (congrArg boundedAboveFlatPerfectNormalizedPullback (first_total P u v).symm) ≪≫
      boundedAboveFlatPerfectNormalizedPullbackCompIso
        (coefficientMap P ((laurentUnderFunctor R).map v))
        (coefficientMap P ((laurentUnderFunctor R).map u) ≫ laurentProjection P a)) ≪≫
    isoWhiskerRight
      (smallIso (eqToIso
        (congrArg boundedAboveFlatPerfectNormalizedPullback (bottomSourceGeom P u)) ≪≫
        boundedAboveFlatPerfectNormalizedPullbackCompIso
        (coefficientMap P ((laurentUnderFunctor R).map u))
          (laurentPlus P a ≫ polynomialProjection P a)))
      (AsSmall.down ⋙ boundedAboveFlatPerfectNormalizedPullback
        (coefficientMap P ((laurentUnderFunctor R).map v)) ⋙ AsSmall.up) =
    smallIso (eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback
      (BoundedFlatCoefficientBassBottomCommonFamily.bottom_total P u v).symm) ≪≫
      boundedAboveFlatPerfectNormalizedPullbackCompIso
        (coefficientMap P ((laurentUnderFunctor R).map v) ≫
          coefficientMap P ((laurentUnderFunctor R).map u))
        (laurentPlus P a ≫ polynomialProjection P a)) ≪≫
    isoWhiskerLeft (AsSmall.down ⋙ boundedAboveFlatPerfectNormalizedPullback
      (laurentPlus P a ≫ polynomialProjection P a) ⋙ AsSmall.up)
      (smallIso (boundedAboveFlatPerfectNormalizedPullbackCompIso
        (coefficientMap P ((laurentUnderFunctor R).map v))
        (coefficientMap P ((laurentUnderFunctor R).map u))))
  rw [smallIso_postcomp, smallIso_precomp, ← smallIso_trans, ← smallIso_trans]
  apply congrArg smallIso
  simpa only [eqToIso_refl, Iso.refl_trans, Iso.trans_assoc] using
    (anchored_factorizations_strict
      (coefficientMap P ((laurentUnderFunctor R).map v))
      (coefficientMap P ((laurentUnderFunctor R).map u))
      (laurentPlus P a ≫ polynomialProjection P a)
      (coefficientMap P ((laurentUnderFunctor R).map v) ≫
        coefficientMap P ((laurentUnderFunctor R).map u))
      (coefficientMap P ((laurentUnderFunctor R).map u) ≫ laurentProjection P a)
      (laurentProjection P c ≫ coefficientMap P v ≫ coefficientMap P u)
      rfl (bottomSourceGeom P u)
      (BoundedFlatCoefficientBassBottomCommonFamily.bottom_total P u v).symm
      (first_total P u v).symm).symm

/-- Full original first/bottom central node, before any larger relabeling. -/
theorem first_bottom_center : BoundedFlatCoefficientBassH1References.firstNodes P u v 2 =
    BoundedFlatCoefficientBassBottomCommonFamily.bottomNodes P u v 2 := by
  rw [first_bottom_center_original, bottom_target_center_original]
  apply Sigma.ext
  · apply WideSubcategory.hom_ext
    exact SmallWaldhausenCategory.Hom.ext (bottom_center_functor P u v)
  · have href := heq_of_eq (bottom_center_reference P u v)
    exact href

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1Join
