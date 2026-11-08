/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteScalarTriangle
public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingPrimeTorComparison
public import Colib.AlgebraicGeometry.Correspondences.Composition.FirstStageAmbientStalkSquare

/-!
# The unchanged original remaining list on the full finite model

At an actual closed-fibre point of the whole finite model, its scalar germ agrees with the
original image-to-exterior stalk map. The proof uses the native closed-point stalk identity
for `fromSpecStalk`, the actual pullback square, and native stalk-map composition. Inverting
the localization projection's stalk map therefore recovers the actual exterior scalar map.

The image middle pair and the original sixfold second middle pair commute with the actual
first-stage inclusion. At any original triple point over the image point this gives their
literal stalk-map equality, with both actual point transports retained. Consequently a list
chosen in the original sixfold Z self-product stalk is carried, entry by entry and in the
same order, to its original first-stage list. No list is replaced by generators of its ideal.

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

private theorem remaining_transported_stalkMap_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) (y : Y) (z : Z)
    (hxy : y = f x) (hyz : z = g y) :
    ((Z.presheaf.stalkCongr (Inseparable.of_eq hyz)).hom ≫ g.stalkMap y) ≫
      ((Y.presheaf.stalkCongr (Inseparable.of_eq hxy)).hom ≫ f.stalkMap x) =
    (Z.presheaf.stalkCongr (Inseparable.of_eq (hyz.trans (congrArg g hxy)))).hom ≫
      (f ≫ g).stalkMap x := by
  subst y
  subst z
  simp [TopCat.Presheaf.stalkCongr, Scheme.Hom.stalkMap_comp]

private theorem remaining_transported_stalkMap_congr {X Y : Scheme.{u}}
    (f g : X ⟶ Y) (hfg : f = g) (x : X) (y : Y) (hf : y = f x) (hg : y = g x) :
    (Y.presheaf.stalkCongr (Inseparable.of_eq hf)).hom ≫ f.stalkMap x =
      (Y.presheaf.stalkCongr (Inseparable.of_eq hg)).hom ≫ g.stalkMap x := by
  subst g
  rfl

private theorem remaining_fromSpecStalk_closed_germ (T : Scheme.{u}) (t : T)
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

/-- The actual image middle map is the original sixfold second middle map on the first stage. -/
@[reassoc]
theorem correspondenceLeftIntermediateImageMap_middlePair :
    correspondenceLeftIntermediateImageMap f g h i z w v ≫
        correspondenceLeftImageMiddlePair f g h i z w v =
      correspondenceLeftIntermediateAmbientInclusion f g h i z w v ≫
        correspondenceSixfoldSecondMiddlePair f g h i := by
  rw [← correspondenceLeftImageProductInclusion_middlePair, ← Category.assoc,
    correspondenceLeftIntermediateImageMap_inclusion,
    ← correspondenceRemainingSupportMap_eq, Category.assoc,
    correspondenceRemainingProjection_middlePair]
  simpa only [correspondenceLeftIntermediateAmbientInclusion, Category.assoc,
    correspondenceFirstDiagonal_secondMiddlePair]

/-- An original triple point above the given image point has the same full exterior image. -/
theorem correspondenceRemainingTriple_image_point_eq
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (y : correspondenceTripleIncidence f g h i z w v)
    (hy : correspondenceTripleToLeftImageIncidence f g h i z w v y = x) :
    correspondenceLeftImageIncidenceInclusion f g h i z w v x =
      correspondenceLeftIntermediateImageMap f g h i z w v
        (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y) := by
  subst x
  exact congrArg (fun m => m y)
    (correspondenceTripleToLeftImageIncidence_inclusion f g h i z w v)

/-- The image and original sixfold Z self-product points coincide, by the actual maps. -/
theorem correspondenceRemainingTriple_middle_point_eq
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (y : correspondenceTripleIncidence f g h i z w v)
    (hy : correspondenceTripleToLeftImageIncidence f g h i z w v y = x) :
    correspondenceLeftImageMiddlePair f g h i z w v
        (correspondenceLeftImageIncidenceInclusion f g h i z w v x) =
      correspondenceSixfoldSecondMiddlePair f g h i
        (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v y) := by
  have he := congrArg (fun m => m
    (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y))
      (correspondenceLeftIntermediateImageMap_middlePair f g h i z w v)
  exact (congrArg (correspondenceLeftImageMiddlePair f g h i z w v)
    (correspondenceRemainingTriple_image_point_eq f g h i z w v x y hy)).trans
      (he.trans (congrArg (correspondenceSixfoldSecondMiddlePair f g h i)
        (correspondenceTripleIncidence_firstStage_point_eq f g h i z w v y).symm))

/-- The image-stalk action on the original first-stage local ring, using its actual map. -/
def correspondenceRemainingImageToFirstStageStalkMap
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (y : correspondenceTripleIncidence f g h i z w v)
    (hy : correspondenceTripleToLeftImageIncidence f g h i z w v y = x) :
    correspondenceRemainingImageStalk f g h i z w v x →+*
      (correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk
        (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y) :=
  (((correspondenceLeftIntermediateImageProduct f g h i z w v).presheaf.stalkCongr
    (Inseparable.of_eq (correspondenceRemainingTriple_image_point_eq
      f g h i z w v x y hy))).hom ≫
        (correspondenceLeftIntermediateImageMap f g h i z w v).stalkMap
          (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y)).hom

/-- The image middle stalk maps to the original sixfold stalk along the actual second pair. -/
def correspondenceRemainingOriginalMiddleStalkMap
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (y : correspondenceTripleIncidence f g h i z w v)
    (hy : correspondenceTripleToLeftImageIncidence f g h i z w v y = x) :
    (pullback h h).presheaf.stalk (correspondenceLeftImageMiddlePair f g h i z w v
      (correspondenceLeftImageIncidenceInclusion f g h i z w v x)) →+*
        correspondenceTripleIncidenceAmbientStalk f g h i z w v y :=
  (((pullback h h).presheaf.stalkCongr (Inseparable.of_eq
    (correspondenceRemainingTriple_middle_point_eq f g h i z w v x y hy))).hom ≫
      (correspondenceSixfoldSecondMiddlePair f g h i).stalkMap
        (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v y)).hom

/-- Both actual middle-scalar routes to the original first-stage local ring agree. -/
theorem correspondenceRemainingImageToFirstStageStalkMap_comp_middle
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (y : correspondenceTripleIncidence f g h i z w v)
    (hy : correspondenceTripleToLeftImageIncidence f g h i z w v y = x) :
    (correspondenceRemainingImageToFirstStageStalkMap f g h i z w v x y hy).comp
        (correspondenceRemainingImageMiddleStalkMap f g h i z w v x) =
      (correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v y).comp
        (correspondenceRemainingOriginalMiddleStalkMap f g h i z w v x y hy) := by
  let a := correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y
  let t := correspondenceLeftImageIncidenceInclusion f g h i z w v x
  let p := correspondenceTripleIncidenceSixfoldInclusion f g h i z w v y
  let b := correspondenceLeftImageMiddlePair f g h i z w v t
  have hleft := remaining_transported_stalkMap_comp
    (correspondenceLeftIntermediateImageMap f g h i z w v)
    (correspondenceLeftImageMiddlePair f g h i z w v) a t b
    (correspondenceRemainingTriple_image_point_eq f g h i z w v x y hy) rfl
  have hright := remaining_transported_stalkMap_comp
    (correspondenceLeftIntermediateAmbientInclusion f g h i z w v)
    (correspondenceSixfoldSecondMiddlePair f g h i) a p b
    (correspondenceTripleIncidence_firstStage_point_eq f g h i z w v y)
    (correspondenceRemainingTriple_middle_point_eq f g h i z w v x y hy)
  have hmaps := remaining_transported_stalkMap_congr
    (correspondenceLeftIntermediateImageMap f g h i z w v ≫
      correspondenceLeftImageMiddlePair f g h i z w v)
    (correspondenceLeftIntermediateAmbientInclusion f g h i z w v ≫
      correspondenceSixfoldSecondMiddlePair f g h i)
    (correspondenceLeftIntermediateImageMap_middlePair f g h i z w v) a b
    (congrArg (correspondenceLeftImageMiddlePair f g h i z w v)
      (correspondenceRemainingTriple_image_point_eq f g h i z w v x y hy))
    ((correspondenceRemainingTriple_middle_point_eq f g h i z w v x y hy).trans
      (congrArg (correspondenceSixfoldSecondMiddlePair f g h i)
        (correspondenceTripleIncidence_firstStage_point_eq f g h i z w v y)))
  have he := hleft.trans (hmaps.trans hright.symm)
  simpa only [correspondenceRemainingImageToFirstStageStalkMap,
    correspondenceRemainingImageMiddleStalkMap, correspondenceRemainingOriginalMiddleStalkMap,
    correspondenceTripleIncidenceFirstStageStalkMap, TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp, a, t, p, b,
    CommRingCat.hom_comp] using congrArg (fun m => m.hom) he

/-- Global functions on the actual model are transported by the inverse of its projection stalk. -/
def correspondenceRemainingFiniteOriginalStalkMap
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (q : correspondenceRemainingFiniteModel f g h i z w v x) :
    correspondenceRemainingFiniteRing f g h i z w v x →+*
      (correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk
        (correspondenceRemainingFiniteModelProjection f g h i z w v x q) := by
  have := isIso_correspondenceRemainingFiniteModelProjection_stalkMap f g h i z w v x q
  exact (((correspondenceRemainingFiniteModel f g h i z w v x).presheaf.germ ⊤ q trivial) ≫
    inv ((correspondenceRemainingFiniteModelProjection f g h i z w v x).stalkMap q)).hom

/-- At a genuine closed-fibre point, the full finite algebra has the original image action. -/
theorem correspondenceRemainingFiniteOriginalStalkMap_comp_algebraMap
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (q : correspondenceRemainingFiniteModel f g h i z w v x)
    (hq : correspondenceRemainingFiniteModelStructure f g h i z w v x q =
      IsLocalRing.closedPoint (correspondenceRemainingImageStalk f g h i z w v x))
    (y : correspondenceTripleIncidence f g h i z w v)
    (hy : correspondenceTripleToLeftImageIncidence f g h i z w v y = x)
    (hρ : correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y =
      correspondenceRemainingFiniteModelProjection f g h i z w v x q) :
    let := correspondenceRemainingFiniteAlgebra f g h i z w v x
    (correspondenceRemainingFiniteOriginalStalkMap f g h i z w v x q).comp
        (algebraMap (correspondenceRemainingImageStalk f g h i z w v x)
          (correspondenceRemainingFiniteRing f g h i z w v x)) =
      ((correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalkCongr
        (Inseparable.of_eq hρ)).hom.hom.comp
          (correspondenceRemainingImageToFirstStageStalkMap f g h i z w v x y hy) := by
  let := correspondenceRemainingFiniteAlgebra f g h i z w v x
  let R := correspondenceRemainingImageStalk f g h i z w v x
  let E := correspondenceRemainingFiniteModel f g h i z w v x
  let T := correspondenceLeftIntermediateImageProduct f g h i z w v
  let F := correspondenceLeftIntermediateSupportProduct f g h i z w v
  let π := correspondenceRemainingFiniteModelStructure f g h i z w v x
  let ρ := correspondenceRemainingFiniteModelProjection f g h i z w v x
  let m := correspondenceLeftIntermediateImageMap f g h i z w v
  let t := correspondenceLeftImageIncidenceInclusion f g h i z w v x
  let a := correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y
  have ht : t = T.fromSpecStalk t (π q) := by
    rw [hq, Scheme.fromSpecStalk_closedPoint]
  have hclosed := remaining_fromSpecStalk_closed_germ T t (π q) hq ht
  have hleft := remaining_transported_stalkMap_comp π (T.fromSpecStalk t)
    q (π q) t rfl ht
  have hright := remaining_transported_stalkMap_comp ρ m q a t hρ
    (correspondenceRemainingTriple_image_point_eq f g h i z w v x y hy)
  have hmaps := remaining_transported_stalkMap_congr
    (π ≫ T.fromSpecStalk t) (ρ ≫ m) pullback.condition.symm q t ht
    ((correspondenceRemainingTriple_image_point_eq f g h i z w v x y hy).trans
      (congrArg m hρ))
  have he := hleft.trans (hmaps.trans hright.symm)
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp] at hclosed he
  rw [← hclosed] at he
  have hscalar := correspondenceRemainingFiniteAlgebra_germ f g h i z w v x q
  have hgerm : (CommRingCat.ofHom (algebraMap R
      (correspondenceRemainingFiniteRing f g h i z w v x))) ≫
        E.presheaf.germ ⊤ q trivial =
      ((T.presheaf.stalkCongr (Inseparable.of_eq
        (correspondenceRemainingTriple_image_point_eq f g h i z w v x y hy))).hom ≫
          m.stalkMap a) ≫ (F.presheaf.stalkCongr (Inseparable.of_eq hρ)).hom ≫
            ρ.stalkMap q := by
    apply CommRingCat.hom_ext
    exact hscalar.trans (congrArg (fun k => k.hom) he)
  have := isIso_correspondenceRemainingFiniteModelProjection_stalkMap f g h i z w v x q
  have hinv := congrArg (fun k => k ≫ inv (ρ.stalkMap q)) hgerm
  simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id,
    correspondenceRemainingFiniteOriginalStalkMap, correspondenceRemainingImageToFirstStageStalkMap,
    CommRingCat.hom_comp, R, E, T, F, π, ρ, m, t, a] using
      congrArg (fun k => k.hom) hinv

/-- After the actual inverse projection stalk map, the original remaining scalar maps agree. -/
theorem correspondenceRemainingFiniteOriginalStalkMap_comp_middle
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (q : correspondenceRemainingFiniteModel f g h i z w v x)
    (hq : correspondenceRemainingFiniteModelStructure f g h i z w v x q =
      IsLocalRing.closedPoint (correspondenceRemainingImageStalk f g h i z w v x))
    (y : correspondenceTripleIncidence f g h i z w v)
    (hy : correspondenceTripleToLeftImageIncidence f g h i z w v y = x)
    (hρ : correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y =
      correspondenceRemainingFiniteModelProjection f g h i z w v x q) :
    let := correspondenceRemainingFiniteAlgebra f g h i z w v x
    ((correspondenceRemainingFiniteOriginalStalkMap f g h i z w v x q).comp
        (algebraMap (correspondenceRemainingImageStalk f g h i z w v x)
          (correspondenceRemainingFiniteRing f g h i z w v x))).comp
        (correspondenceRemainingImageMiddleStalkMap f g h i z w v x) =
      ((correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalkCongr
        (Inseparable.of_eq hρ)).hom.hom.comp
          ((correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v y).comp
            (correspondenceRemainingOriginalMiddleStalkMap f g h i z w v x y hy)) := by
  let := correspondenceRemainingFiniteAlgebra f g h i z w v x
  rw [correspondenceRemainingFiniteOriginalStalkMap_comp_algebraMap
    f g h i z w v x q hq y hy hρ, RingHom.comp_assoc,
    correspondenceRemainingImageToFirstStageStalkMap_comp_middle]

/-- The unchanged original sixfold Z-list, not only its generated ideal, survives localization. -/
theorem correspondenceRemainingFiniteOriginalStalkMap_originalList
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (q : correspondenceRemainingFiniteModel f g h i z w v x)
    (hq : correspondenceRemainingFiniteModelStructure f g h i z w v x q =
      IsLocalRing.closedPoint (correspondenceRemainingImageStalk f g h i z w v x))
    (y : correspondenceTripleIncidence f g h i z w v)
    (hy : correspondenceTripleToLeftImageIncidence f g h i z w v y = x)
    (hρ : correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y =
      correspondenceRemainingFiniteModelProjection f g h i z w v x q) {r : ℕ}
    (s : Fin r → (pullback h h).presheaf.stalk
      (correspondenceSixfoldSecondMiddlePair f g h i
        (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v y))) :
    let := correspondenceRemainingFiniteAlgebra f g h i z w v x
    let e := (pullback h h).presheaf.stalkCongr (Inseparable.of_eq
      (correspondenceRemainingTriple_middle_point_eq f g h i z w v x y hy))
    (fun j => correspondenceRemainingFiniteOriginalStalkMap f g h i z w v x q
      (algebraMap (correspondenceRemainingImageStalk f g h i z w v x)
        (correspondenceRemainingFiniteRing f g h i z w v x)
        (correspondenceRemainingImageMiddleStalkMap f g h i z w v x (e.inv (s j))))) =
      (fun j => ((correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalkCongr
        (Inseparable.of_eq hρ)).hom
          (correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v y
            ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap
              (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v y) (s j)))) := by
  let := correspondenceRemainingFiniteAlgebra f g h i z w v x
  let e := (pullback h h).presheaf.stalkCongr (Inseparable.of_eq
    (correspondenceRemainingTriple_middle_point_eq f g h i z w v x y hy))
  have he := correspondenceRemainingFiniteOriginalStalkMap_comp_middle
    f g h i z w v x q hq y hy hρ
  funext j
  have hj := congrArg (fun φ => φ (e.inv (s j))) he
  simpa only [RingHom.comp_apply, correspondenceRemainingOriginalMiddleStalkMap,
    CommRingCat.hom_comp, RingHom.comp_apply, e, Iso.inv_hom_id_apply] using hj

end Stacks.Chow
