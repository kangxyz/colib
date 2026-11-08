/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingImage
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.CoefficientColength
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.Support
public import StacksFrontier.RingTheory.HilbertSamuel.Defs
public import Colib.Algebra.Category.ModuleCat.ChangeOfRings.Quotient

/-!
# The actual remaining Y ideal on the full right image exterior

The first support and the full scheme-theoretic image of G,H are retained in
this order. Their remaining incidence is the actual Y-diagonal base change.
At a generic point of that incidence the full local image kernel is an ideal
of definition. Native Cartesian stalk-kernel base change identifies it with
the original Y ideal, so an original Y generating list has finite colength.

No transposed correspondence, reduction of the image exterior, or flatness of
the finite original-to-image map is used. This is a right geometric supplier
for the whole finite model, not a right coefficient or weighted-cycle equality.

Source target: motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
Composition/Cycles/RightFirstStageWeightedRemainingCoefficient.lean,
blob 5771cc85d24a32f3610872f2a94d457154d1673b. The native generic ideal proof is
reused from the existing left RemainingImageGenericStalk construction, applied
to these actual right maps, without renaming the correspondences themselves.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The actual full right image exterior maps to the original X,Y source product. -/
def correspondenceRightIntermediateImageSourceMap :
    correspondenceRightIntermediateImageProduct f g h i z w v ⟶ pullback f g :=
  pullback.map _ _ f g ((integralComponentAt z).subschemeι ≫ pullback.fst f g)
    ((correspondenceIncidenceMap g h i w v).imageι ≫ pullback.fst g i) (𝟙 S)
    (by simp [Category.assoc, pullback.condition]) (by simp)

/-- Finiteness uses F over X and the actual G,H image over Y, in their original directions. -/
theorem isFinite_correspondenceRightIntermediateImageSourceMap
    [IsSeparated i] [LocallyOfFiniteType i]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (hv : IsFiniteCorrespondencePoint h i v) :
    IsFinite (correspondenceRightIntermediateImageSourceMap f g h i z w v) := by
  let := hz.1
  let := isFinite_correspondenceIntermediateImageSource g h i w v hw hv
  unfold correspondenceRightIntermediateImageSourceMap
  exact MorphismProperty.pullbackMap (P := @IsFinite)
    inferInstance inferInstance (by simp [Category.assoc, pullback.condition]) (by simp)

/-- Local Noetherianness follows from the actual finite map to the original X,Y product. -/
theorem isLocallyNoetherian_correspondenceRightIntermediateImageProduct
    [IsSeparated i] [LocallyOfFiniteType i] [IsLocallyNoetherian (pullback f g)]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (hv : IsFiniteCorrespondencePoint h i v) :
    IsLocallyNoetherian (correspondenceRightIntermediateImageProduct f g h i z w v) := by
  let := isFinite_correspondenceRightIntermediateImageSourceMap f g h i z w v hz hw hv
  exact LocallyOfFiniteType.isLocallyNoetherian
    (correspondenceRightIntermediateImageSourceMap f g h i z w v)

/-- The full exterior is locally Noetherian by its actual finite map to the full image. -/
theorem isLocallyNoetherian_correspondenceRightIntermediateSupportProduct_of_image
    [IsSeparated i]
    [IsLocallyNoetherian (correspondenceRightIntermediateImageProduct f g h i z w v)]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v) :
    IsLocallyNoetherian (correspondenceRightIntermediateSupportProduct f g h i z w v) := by
  let := isFinite_correspondenceRightIntermediateImageMap f g h i z w v hw hv
  exact LocallyOfFiniteType.isLocallyNoetherian
    (correspondenceRightIntermediateImageMap f g h i z w v)

/-- The original middle pair on the full intermediate-image exterior. -/
abbrev correspondenceRightImageMiddlePair :
    correspondenceRightIntermediateImageProduct f g h i z w v ⟶ pullback g g :=
  pullback.map _ _ g g ((integralComponentAt z).subschemeι ≫ pullback.snd f g)
    ((correspondenceIncidenceMap g h i w v).imageι ≫ pullback.fst g i) (𝟙 S) (by simp) (by simp)

/-- The remaining incidence of the full image is the original middle-diagonal pullback. -/
theorem correspondenceRightImageMiddlePair_isPullback :
    IsPullback (correspondenceRightImageIncidenceInclusion f g h i z w v)
      (pullback.fst ((integralComponentAt z).subschemeι ≫ pullback.snd f g)
        ((correspondenceIncidenceMap g h i w v).imageι ≫ pullback.fst g i) ≫
          ((integralComponentAt z).subschemeι ≫ pullback.snd f g))
      (correspondenceRightImageMiddlePair f g h i z w v) (pullback.diagonal g) :=
  (pullback_map_diagonal_isPullback ((integralComponentAt z).subschemeι ≫ pullback.snd f g)
    ((correspondenceIncidenceMap g h i w v).imageι ≫ pullback.fst g i) g).flip

/-- The full image-exterior local ring at a remaining-incidence point. -/
abbrev correspondenceRightRemainingImageStalk
    (x : correspondenceRightImageIncidence f g h i z w v) :=
  (correspondenceRightIntermediateImageProduct f g h i z w v).presheaf.stalk
    (correspondenceRightImageIncidenceInclusion f g h i z w v x)

/-- The original middle self-product stalk maps to the actual full image-exterior stalk. -/
abbrev correspondenceRightRemainingImageMiddleStalkMap
    (x : correspondenceRightImageIncidence f g h i z w v) :
    (pullback g g).presheaf.stalk (correspondenceRightImageMiddlePair f g h i z w v
      (correspondenceRightImageIncidenceInclusion f g h i z w v x)) →+*
        correspondenceRightRemainingImageStalk f g h i z w v x :=
  ((correspondenceRightImageMiddlePair f g h i z w v).stalkMap
    (correspondenceRightImageIncidenceInclusion f g h i z w v x)).hom

/-- The kernel in the full image-exterior stalk is an ideal of definition
at each actual generic remaining-image incidence label. -/
theorem isIdealOfDefinition_correspondenceRightRemainingImageStalkKernel [IsSeparated g]
    [IsLocallyNoetherian (correspondenceRightIntermediateImageProduct f g h i z w v)]
    (x : genericPoints (correspondenceRightImageIncidence f g h i z w v)) :
    IsIdealOfDefinition (RingHom.ker
      ((correspondenceRightImageIncidenceInclusion f g h i z w v).stalkMap x.1).hom) := by
  let := LocallyOfFiniteType.isLocallyNoetherian
    (correspondenceRightImageIncidenceInclusion f g h i z w v)
  let := generic_stalk_artinian x
  change Ideal.radical (RingHom.ker
    ((correspondenceRightImageIncidenceInclusion f g h i z w v).stalkMap x.1).hom) = _
  rw [RingHom.ker_eq_comap_bot, ← Ideal.comap_radical,
    ← IsArtinianRing.jacobson_eq_radical,
    IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top,
    IsLocalRing.maximalIdeal_comap]

/-- The full remaining-image kernel is generated by the original middle
self-product diagonal ideal under its original stalk map. -/
theorem correspondenceRightRemainingImageStalkKernel_eq_map [IsSeparated g]
    (x : correspondenceRightImageIncidence f g h i z w v) :
    RingHom.ker ((correspondenceRightImageIncidenceInclusion f g h i z w v).stalkMap x).hom =
      (IdealSheafData.stalk (pullback.diagonal g).ker
        (correspondenceRightImageMiddlePair f g h i z w v
          (correspondenceRightImageIncidenceInclusion f g h i z w v x))).map
            (correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x) := by
  let H := correspondenceRightImageMiddlePair_isPullback f g h i z w v
  have hp : pullback.diagonal g
      ((pullback.fst ((integralComponentAt z).subschemeι ≫ pullback.snd f g)
        ((correspondenceIncidenceMap g h i w v).imageι ≫ pullback.fst g i) ≫
          ((integralComponentAt z).subschemeι ≫ pullback.snd f g)) x) =
      correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x) := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun m => m x) H.w.symm
  have hk := Stacks.Flatness.ker_stalkMap_of_isPullback H x hp
  rw [ker_stalkMap_eq_idealStalk_ker (pullback.diagonal g)
    ((pullback.fst ((integralComponentAt z).subschemeι ≫ pullback.snd f g)
      ((correspondenceIncidenceMap g h i w v).imageι ≫ pullback.fst g i) ≫
        ((integralComponentAt z).subschemeι ≫ pullback.snd f g)) x),
    CommRingCat.hom_comp, ← Ideal.map_map] at hk
  have htransport {p q : pullback (C := Scheme) g g} (e : p = q) :
      (IdealSheafData.stalk (pullback.diagonal g).ker p).map
        ((pullback g g).presheaf.stalkCongr (Inseparable.of_eq e)).hom.hom =
          IdealSheafData.stalk (pullback.diagonal g).ker q := by
    subst q
    simp [TopCat.Presheaf.stalkCongr]
  rw [htransport hp] at hk
  exact hk

/-- The actual generic remaining-image intersection proves finite colength
for the literal mapped original middle list, including nilpotents. -/
theorem isIdealOfDefinition_correspondenceRightRemainingImageMiddleList [IsSeparated g]
    [IsLocallyNoetherian (correspondenceRightIntermediateImageProduct f g h i z w v)]
    (x : genericPoints (correspondenceRightImageIncidence f g h i z w v)) {r : ℕ}
    (s : Fin r → (pullback g g).presheaf.stalk
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x.1)))
    (hs : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x.1)) =
          Ideal.span (Set.range s)) :
    IsIdealOfDefinition (Ideal.span (Set.range (fun j =>
      correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x.1 (s j)))) := by
  have hi := isIdealOfDefinition_correspondenceRightRemainingImageStalkKernel f g h i z w v x
  rw [correspondenceRightRemainingImageStalkKernel_eq_map, hs,
    Ideal.map_span, ← Set.range_comp'] at hi
  exact hi

end Stacks.Chow
