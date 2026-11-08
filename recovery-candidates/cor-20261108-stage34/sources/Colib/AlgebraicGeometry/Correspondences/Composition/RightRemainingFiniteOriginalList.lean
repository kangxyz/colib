/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteScalarTriangle
public import Colib.AlgebraicGeometry.Correspondences.Composition.RightCommonImageSquare
public import Colib.AlgebraicGeometry.Correspondences.Composition.RightFirstStageAction

/-!
# The unchanged original remaining Y list on the full right finite model

At an actual closed-fibre point of the whole finite model, its scalar germ agrees with the
original image-to-exterior stalk map. The proof uses the native closed-point stalk identity
for `fromSpecStalk`, the actual pullback square, and native stalk-map composition. Inverting
the localization projection's stalk map therefore recovers the actual exterior scalar map.

The image middle pair and the original sixfold first middle pair commute with the actual
first-stage inclusion. At any original triple point over the image point this gives their
literal stalk-map equality, with both actual point transports retained. Consequently a list
chosen in the original sixfold Y self-product stalk is carried, entry by entry and in the
same order, to its original right first-stage list. No list is replaced by generators of its ideal.

The only hypotheses on points are membership in the actual closed fibre, the actual
triple-to-image fibre equality, and equality of their original exterior projections. There
is no supplied ring or module comparison, finite-map flatness, regularity hypothesis,
reduction, field assumption, or connectedness assumption.

## References and scope

* Mathlib `AlgebraicGeometry/Stalk.lean`, `stalkClosedPointTo_fromSpecStalk` and
  `germ_stalkClosedPointIso_hom`: the local-scheme scalar identity used here.
* Mathlib `AlgebraicGeometry/Scheme.lean`, `Scheme.Hom.stalkMap_comp` and
  `Scheme.Hom.stalkMap_congr_hom`: functoriality with actual point transport.
* The original ordered diagonal lists are those in `TripleOriginalMiddleLists`, adapted
  from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380, `TripleIdeals.lean` and
  `CommonRegularity.lean`. This file supplies their scalar compatibility, not a new
  regular-sequence, Tor-module, or finite-pushforward Euler comparison.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

private theorem right_remaining_transported_stalkMap_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) (y : Y) (z : Z)
    (hxy : y = f x) (hyz : z = g y) :
    ((Z.presheaf.stalkCongr (Inseparable.of_eq hyz)).hom ≫ g.stalkMap y) ≫
      ((Y.presheaf.stalkCongr (Inseparable.of_eq hxy)).hom ≫ f.stalkMap x) =
    (Z.presheaf.stalkCongr (Inseparable.of_eq (hyz.trans (congrArg g hxy)))).hom ≫
      (f ≫ g).stalkMap x := by
  subst y
  subst z
  simp [TopCat.Presheaf.stalkCongr, Scheme.Hom.stalkMap_comp]

private theorem right_remaining_transported_stalkMap_congr {X Y : Scheme.{u}}
    (f g : X ⟶ Y) (hfg : f = g) (x : X) (y : Y) (hf : y = f x) (hg : y = g x) :
    (Y.presheaf.stalkCongr (Inseparable.of_eq hf)).hom ≫ f.stalkMap x =
      (Y.presheaf.stalkCongr (Inseparable.of_eq hg)).hom ≫ g.stalkMap x := by
  subst g
  rfl

private theorem right_remaining_fromSpecStalk_closed_germ (T : Scheme.{u}) (t : T)
    (p : Spec (T.presheaf.stalk t))
    (hp : p = IsLocalRing.closedPoint (T.presheaf.stalk t))
    (ht : t = T.fromSpecStalk t p) :
    (Scheme.ΓSpecIso (T.presheaf.stalk t)).inv ≫ (Spec (T.presheaf.stalk t)).presheaf.germ
        ⊤ p trivial =
      (T.presheaf.stalkCongr (Inseparable.of_eq ht)).hom ≫ (T.fromSpecStalk t).stalkMap p := by
  subst p
  apply (cancel_mono (stalkClosedPointIso (T.presheaf.stalk t)).hom).mp
  rw [Category.assoc, germ_stalkClosedPointIso_hom, Iso.inv_hom_id]
  rw [Category.assoc, ← Scheme.stalkClosedPointTo, Scheme.stalkClosedPointTo_fromSpecStalk]
  simp [TopCat.Presheaf.stalkCongr]

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The actual image middle map is the original sixfold first middle map on the first stage. -/
@[reassoc]
theorem correspondenceRightIntermediateImageMap_middlePair :
    correspondenceRightIntermediateImageMap f g h i z w v ≫
        correspondenceRightImageMiddlePair f g h i z w v =
      correspondenceRightIntermediateAmbientInclusion f g h i z w v ≫
        correspondenceSixfoldFirstMiddlePair f g h i := by
  have hfst : correspondenceSixfoldFirstMiddlePair f g h i ≫ pullback.fst g g =
      correspondenceSixfoldFirstFactorProjection f g h i ≫ pullback.snd f g := by
    simp [correspondenceSixfoldFirstMiddlePair, correspondenceSixfoldFirstFactorProjection,
      correspondenceMiddlePair, Category.assoc]
  have hsnd : correspondenceSixfoldFirstMiddlePair f g h i ≫ pullback.snd g g =
      correspondenceSixfoldRightPairProjection f g h i ≫ correspondenceAmbientSource g h i := by
    simp [correspondenceSixfoldFirstMiddlePair, correspondenceSixfoldRightPairProjection,
      correspondenceAmbientSource, correspondenceMiddlePair, Category.assoc]
  apply pullback.hom_ext
  · simp [Category.assoc, hfst, correspondenceRightIntermediateAmbientInclusion,
      correspondenceRightImageMiddlePair, correspondenceRightIntermediateImageMap]
  · simp [Category.assoc, hsnd, correspondenceRightIntermediateAmbientInclusion,
      correspondenceRightImageMiddlePair, correspondenceRightIntermediateImageMap,
      correspondenceAmbientSource, correspondenceTripleInclusion, correspondenceIncidenceInclusion,
      correspondenceIncidenceLeft, correspondenceRightExteriorProjection]

/-- An original triple point above the given image point has the same full exterior image. -/
theorem correspondenceRightRemainingTriple_image_point_eq
    (x : correspondenceRightImageIncidence f g h i z w v)
    (y : correspondenceTripleIncidence f g h i z w v)
    (hy : correspondenceTripleToRightImageIncidence f g h i z w v y = x) :
    correspondenceRightImageIncidenceInclusion f g h i z w v x =
      correspondenceRightIntermediateImageMap f g h i z w v
        (correspondenceTripleIncidenceToRightSupportProduct f g h i z w v y) := by
  subst x
  exact congrArg (fun m => m y)
    (correspondenceTripleToRightImageIncidence_inclusion f g h i z w v)

/-- The image and original sixfold Y self-product points coincide, by the actual maps. -/
theorem correspondenceRightRemainingTriple_middle_point_eq
    (x : correspondenceRightImageIncidence f g h i z w v)
    (y : correspondenceTripleIncidence f g h i z w v)
    (hy : correspondenceTripleToRightImageIncidence f g h i z w v y = x) :
    correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x) =
      correspondenceSixfoldFirstMiddlePair f g h i
        (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v y) := by
  have he := congrArg (fun m => m
    (correspondenceTripleIncidenceToRightSupportProduct f g h i z w v y))
      (correspondenceRightIntermediateImageMap_middlePair f g h i z w v)
  exact (congrArg (correspondenceRightImageMiddlePair f g h i z w v)
    (correspondenceRightRemainingTriple_image_point_eq f g h i z w v x y hy)).trans
      (he.trans (congrArg (correspondenceSixfoldFirstMiddlePair f g h i)
        (correspondenceTripleIncidence_rightFirstStage_point_eq f g h i z w v y).symm))

/-- The image-stalk action on the original right first-stage local ring, using its actual map. -/
def correspondenceRightRemainingImageToFirstStageStalkMap
    (x : correspondenceRightImageIncidence f g h i z w v)
    (y : correspondenceTripleIncidence f g h i z w v)
    (hy : correspondenceTripleToRightImageIncidence f g h i z w v y = x) :
    correspondenceRightRemainingImageStalk f g h i z w v x →+*
      (correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk
        (correspondenceTripleIncidenceToRightSupportProduct f g h i z w v y) :=
  (((correspondenceRightIntermediateImageProduct f g h i z w v).presheaf.stalkCongr
    (Inseparable.of_eq (correspondenceRightRemainingTriple_image_point_eq
      f g h i z w v x y hy))).hom ≫
        (correspondenceRightIntermediateImageMap f g h i z w v).stalkMap
          (correspondenceTripleIncidenceToRightSupportProduct f g h i z w v y)).hom

/-- The image middle stalk maps to the original sixfold stalk along the actual first middle pair. -/
def correspondenceRightRemainingOriginalMiddleStalkMap
    (x : correspondenceRightImageIncidence f g h i z w v)
    (y : correspondenceTripleIncidence f g h i z w v)
    (hy : correspondenceTripleToRightImageIncidence f g h i z w v y = x) :
    (pullback g g).presheaf.stalk (correspondenceRightImageMiddlePair f g h i z w v
      (correspondenceRightImageIncidenceInclusion f g h i z w v x)) →+*
        correspondenceTripleIncidenceAmbientStalk f g h i z w v y :=
  (((pullback g g).presheaf.stalkCongr (Inseparable.of_eq
    (correspondenceRightRemainingTriple_middle_point_eq f g h i z w v x y hy))).hom ≫
      (correspondenceSixfoldFirstMiddlePair f g h i).stalkMap
        (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v y)).hom

/-- Both actual middle-scalar routes to the original right first-stage local ring agree. -/
theorem correspondenceRightRemainingImageToFirstStageStalkMap_comp_middle
    (x : correspondenceRightImageIncidence f g h i z w v)
    (y : correspondenceTripleIncidence f g h i z w v)
    (hy : correspondenceTripleToRightImageIncidence f g h i z w v y = x) :
    (correspondenceRightRemainingImageToFirstStageStalkMap f g h i z w v x y hy).comp
        (correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x) =
      (correspondenceTripleIncidenceRightFirstStageStalkMap f g h i z w v y).comp
        (correspondenceRightRemainingOriginalMiddleStalkMap f g h i z w v x y hy) := by
  let a := correspondenceTripleIncidenceToRightSupportProduct f g h i z w v y
  let t := correspondenceRightImageIncidenceInclusion f g h i z w v x
  let p := correspondenceTripleIncidenceSixfoldInclusion f g h i z w v y
  let b := correspondenceRightImageMiddlePair f g h i z w v t
  have hleft := right_remaining_transported_stalkMap_comp
    (correspondenceRightIntermediateImageMap f g h i z w v)
    (correspondenceRightImageMiddlePair f g h i z w v) a t b
    (correspondenceRightRemainingTriple_image_point_eq f g h i z w v x y hy) rfl
  have hright := right_remaining_transported_stalkMap_comp
    (correspondenceRightIntermediateAmbientInclusion f g h i z w v)
    (correspondenceSixfoldFirstMiddlePair f g h i) a p b
    (correspondenceTripleIncidence_rightFirstStage_point_eq f g h i z w v y)
    (correspondenceRightRemainingTriple_middle_point_eq f g h i z w v x y hy)
  have hmaps := right_remaining_transported_stalkMap_congr
    (correspondenceRightIntermediateImageMap f g h i z w v ≫
      correspondenceRightImageMiddlePair f g h i z w v)
    (correspondenceRightIntermediateAmbientInclusion f g h i z w v ≫
      correspondenceSixfoldFirstMiddlePair f g h i)
    (correspondenceRightIntermediateImageMap_middlePair f g h i z w v) a b
    (congrArg (correspondenceRightImageMiddlePair f g h i z w v)
      (correspondenceRightRemainingTriple_image_point_eq f g h i z w v x y hy))
    ((correspondenceRightRemainingTriple_middle_point_eq f g h i z w v x y hy).trans
      (congrArg (correspondenceSixfoldFirstMiddlePair f g h i)
        (correspondenceTripleIncidence_rightFirstStage_point_eq f g h i z w v y)))
  have he := hleft.trans (hmaps.trans hright.symm)
  simpa only [correspondenceRightRemainingImageToFirstStageStalkMap,
    correspondenceRightRemainingImageMiddleStalkMap,
    correspondenceRightRemainingOriginalMiddleStalkMap,
    correspondenceTripleIncidenceRightFirstStageStalkMap, TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp, a, t, p, b,
    CommRingCat.hom_comp] using congrArg (fun m => m.hom) he

/-- Global functions on the actual model are transported by the inverse of its projection stalk. -/
def correspondenceRightRemainingFiniteOriginalStalkMap
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : correspondenceRightRemainingFiniteModel f g h i z w v x) :
    correspondenceRightRemainingFiniteRing f g h i z w v x →+*
      (correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk
        (correspondenceRightRemainingFiniteModelProjection f g h i z w v x q) := by
  have := isIso_correspondenceRightRemainingFiniteModelProjection_stalkMap f g h i z w v x q
  exact (((correspondenceRightRemainingFiniteModel f g h i z w v x).presheaf.germ ⊤ q trivial) ≫
    inv ((correspondenceRightRemainingFiniteModelProjection f g h i z w v x).stalkMap q)).hom

/-- At a genuine closed-fibre point, the full finite algebra has the original image action. -/
theorem correspondenceRightRemainingFiniteOriginalStalkMap_comp_algebraMap
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : correspondenceRightRemainingFiniteModel f g h i z w v x)
    (hq : correspondenceRightRemainingFiniteModelStructure f g h i z w v x q =
      IsLocalRing.closedPoint (correspondenceRightRemainingImageStalk f g h i z w v x))
    (y : correspondenceTripleIncidence f g h i z w v)
    (hy : correspondenceTripleToRightImageIncidence f g h i z w v y = x)
    (hρ : correspondenceTripleIncidenceToRightSupportProduct f g h i z w v y =
      correspondenceRightRemainingFiniteModelProjection f g h i z w v x q) :
    let := correspondenceRightRemainingFiniteAlgebra f g h i z w v x
    (correspondenceRightRemainingFiniteOriginalStalkMap f g h i z w v x q).comp
        (algebraMap (correspondenceRightRemainingImageStalk f g h i z w v x)
          (correspondenceRightRemainingFiniteRing f g h i z w v x)) =
      ((correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalkCongr
        (Inseparable.of_eq hρ)).hom.hom.comp
          (correspondenceRightRemainingImageToFirstStageStalkMap f g h i z w v x y hy) := by
  let := correspondenceRightRemainingFiniteAlgebra f g h i z w v x
  let R := correspondenceRightRemainingImageStalk f g h i z w v x
  let E := correspondenceRightRemainingFiniteModel f g h i z w v x
  let T := correspondenceRightIntermediateImageProduct f g h i z w v
  let F := correspondenceRightIntermediateSupportProduct f g h i z w v
  let π := correspondenceRightRemainingFiniteModelStructure f g h i z w v x
  let ρ := correspondenceRightRemainingFiniteModelProjection f g h i z w v x
  let m := correspondenceRightIntermediateImageMap f g h i z w v
  let t := correspondenceRightImageIncidenceInclusion f g h i z w v x
  let a := correspondenceTripleIncidenceToRightSupportProduct f g h i z w v y
  have ht : t = T.fromSpecStalk t (π q) := by
    rw [hq, Scheme.fromSpecStalk_closedPoint]
  have hclosed := right_remaining_fromSpecStalk_closed_germ T t (π q) hq ht
  have hleft := right_remaining_transported_stalkMap_comp π (T.fromSpecStalk t)
    q (π q) t rfl ht
  have hright := right_remaining_transported_stalkMap_comp ρ m q a t hρ
    (correspondenceRightRemainingTriple_image_point_eq f g h i z w v x y hy)
  have hmaps := right_remaining_transported_stalkMap_congr
    (π ≫ T.fromSpecStalk t) (ρ ≫ m) pullback.condition.symm q t ht
    ((correspondenceRightRemainingTriple_image_point_eq f g h i z w v x y hy).trans
      (congrArg m hρ))
  have he := hleft.trans (hmaps.trans hright.symm)
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp] at hclosed he
  rw [← hclosed] at he
  have hscalar := correspondenceRightRemainingFiniteAlgebra_germ f g h i z w v x q
  have hgerm : (CommRingCat.ofHom (algebraMap R
      (correspondenceRightRemainingFiniteRing f g h i z w v x))) ≫
        E.presheaf.germ ⊤ q trivial =
      ((T.presheaf.stalkCongr (Inseparable.of_eq
        (correspondenceRightRemainingTriple_image_point_eq f g h i z w v x y hy))).hom ≫
          m.stalkMap a) ≫ (F.presheaf.stalkCongr (Inseparable.of_eq hρ)).hom ≫
            ρ.stalkMap q := by
    apply CommRingCat.hom_ext
    exact hscalar.trans (congrArg (fun k => k.hom) he)
  have := isIso_correspondenceRightRemainingFiniteModelProjection_stalkMap f g h i z w v x q
  have hinv := congrArg (fun k => k ≫ inv (ρ.stalkMap q)) hgerm
  simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id,
    correspondenceRightRemainingFiniteOriginalStalkMap,
    correspondenceRightRemainingImageToFirstStageStalkMap,
    CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_assoc,
    R, E, T, F, π, ρ, m, t, a] using
      congrArg (fun k => k.hom) hinv

/-- After the actual inverse projection stalk map, the original remaining scalar maps agree. -/
theorem correspondenceRightRemainingFiniteOriginalStalkMap_comp_middle
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : correspondenceRightRemainingFiniteModel f g h i z w v x)
    (hq : correspondenceRightRemainingFiniteModelStructure f g h i z w v x q =
      IsLocalRing.closedPoint (correspondenceRightRemainingImageStalk f g h i z w v x))
    (y : correspondenceTripleIncidence f g h i z w v)
    (hy : correspondenceTripleToRightImageIncidence f g h i z w v y = x)
    (hρ : correspondenceTripleIncidenceToRightSupportProduct f g h i z w v y =
      correspondenceRightRemainingFiniteModelProjection f g h i z w v x q) :
    let := correspondenceRightRemainingFiniteAlgebra f g h i z w v x
    ((correspondenceRightRemainingFiniteOriginalStalkMap f g h i z w v x q).comp
        (algebraMap (correspondenceRightRemainingImageStalk f g h i z w v x)
          (correspondenceRightRemainingFiniteRing f g h i z w v x))).comp
        (correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x) =
      ((correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalkCongr
        (Inseparable.of_eq hρ)).hom.hom.comp
          ((correspondenceTripleIncidenceRightFirstStageStalkMap f g h i z w v y).comp
            (correspondenceRightRemainingOriginalMiddleStalkMap f g h i z w v x y hy)) := by
  let := correspondenceRightRemainingFiniteAlgebra f g h i z w v x
  dsimp only
  rw [correspondenceRightRemainingFiniteOriginalStalkMap_comp_algebraMap
    f g h i z w v x q hq y hy hρ, RingHom.comp_assoc,
    correspondenceRightRemainingImageToFirstStageStalkMap_comp_middle]

/-- The unchanged original sixfold Y-list, not only its generated ideal, survives localization. -/
theorem correspondenceRightRemainingFiniteOriginalStalkMap_originalList
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : correspondenceRightRemainingFiniteModel f g h i z w v x)
    (hq : correspondenceRightRemainingFiniteModelStructure f g h i z w v x q =
      IsLocalRing.closedPoint (correspondenceRightRemainingImageStalk f g h i z w v x))
    (y : correspondenceTripleIncidence f g h i z w v)
    (hy : correspondenceTripleToRightImageIncidence f g h i z w v y = x)
    (hρ : correspondenceTripleIncidenceToRightSupportProduct f g h i z w v y =
      correspondenceRightRemainingFiniteModelProjection f g h i z w v x q) {r : ℕ}
    (s : Fin r → (pullback g g).presheaf.stalk
      (correspondenceSixfoldFirstMiddlePair f g h i
        (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v y))) :
    let := correspondenceRightRemainingFiniteAlgebra f g h i z w v x
    let e := (pullback g g).presheaf.stalkCongr (Inseparable.of_eq
      (correspondenceRightRemainingTriple_middle_point_eq f g h i z w v x y hy))
    (fun j => correspondenceRightRemainingFiniteOriginalStalkMap f g h i z w v x q
      (algebraMap (correspondenceRightRemainingImageStalk f g h i z w v x)
        (correspondenceRightRemainingFiniteRing f g h i z w v x)
        (correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x (e.inv (s j))))) =
      (fun j => ((correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalkCongr
        (Inseparable.of_eq hρ)).hom
          (correspondenceTripleIncidenceRightFirstStageStalkMap f g h i z w v y
            ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap
              (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v y) (s j)))) := by
  let := correspondenceRightRemainingFiniteAlgebra f g h i z w v x
  let e := (pullback g g).presheaf.stalkCongr (Inseparable.of_eq
    (correspondenceRightRemainingTriple_middle_point_eq f g h i z w v x y hy))
  have he := correspondenceRightRemainingFiniteOriginalStalkMap_comp_middle
    f g h i z w v x q hq y hy hρ
  funext j
  have hj := congrArg (fun φ => φ (e.inv (s j))) he
  simpa only [RingHom.comp_apply, correspondenceRightRemainingOriginalMiddleStalkMap,
    CommRingCat.hom_comp, RingHom.comp_apply, e, Iso.inv_hom_id_apply] using hj

end Stacks.Chow
