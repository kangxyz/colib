/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightStagePairTorBaseChange
public import Colib.AlgebraicGeometry.Correspondences.Composition.PairOriginalKoszulTor
public import Colib.AlgebraicGeometry.Correspondences.Composition.RightFirstStageAction

/-!
# Actual last-pair and common sixfold scalar maps for Z-first homology

The maps are the genuine right-coordinate projections in the same common
sixfold and full support schemes. Every equality of their images is carried
through the native stalk congruence. In particular, reassociation of the common
support point is not silently treated as definitional equality.

The literal original Z list is mapped by the actual second-middle projection.
The full right-stage quotient action factors through the same support scalar
map used in the coefficient complex. No comparison of actions is an input.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

private theorem transported_stalkMap_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : X) (y : Y) (z : Z) (hxy : y = f x) (hyz : z = g y) :
    ((Z.presheaf.stalkCongr (Inseparable.of_eq hyz)).hom ≫ g.stalkMap y) ≫
      ((Y.presheaf.stalkCongr (Inseparable.of_eq hxy)).hom ≫ f.stalkMap x) =
    (Z.presheaf.stalkCongr (Inseparable.of_eq (hyz.trans (congrArg g hxy)))).hom ≫
      (f ≫ g).stalkMap x := by
  subst y
  subst z
  simp [TopCat.Presheaf.stalkCongr, Scheme.Hom.stalkMap_comp]

private theorem transported_stalkMap_congr {X Y : Scheme.{u}} (f g : X ⟶ Y) (hfg : f = g)
    (x : X) (y : Y) (hf : y = f x) (hg : y = g x) :
    (Y.presheaf.stalkCongr (Inseparable.of_eq hf)).hom ≫ f.stalkMap x =
      (Y.presheaf.stalkCongr (Inseparable.of_eq hg)).hom ≫ g.stalkMap x := by
  subst g
  rfl


variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The actual right stage commutes with the last-pair ambient projection. -/
@[reassoc]
theorem correspondenceRightIntermediateAmbientInclusion_pairProjection :
    correspondenceRightIntermediateAmbientInclusion f g h i z w v ≫
      correspondenceSixfoldRightPairProjection f g h i =
    correspondenceRightExteriorProjection f g h i z w v ≫
      correspondenceIncidenceAmbientInclusion g h i w v := by
  simp only [correspondenceRightIntermediateAmbientInclusion, Category.assoc,
    correspondenceSecondAmbientInclusion_rightPair,
    correspondenceRightIntermediateSupportInclusion_rightPair_assoc]

/-- The literal Z middle pair is retained by the native right ambient projection. -/
@[reassoc]
theorem correspondenceSixfoldRightPairProjection_middlePair :
    correspondenceSixfoldRightPairProjection f g h i ≫ correspondenceMiddlePair g h i =
      correspondenceSixfoldSecondMiddlePair f g h i := by
  apply pullback.hom_ext <;>
    simp [correspondenceSixfoldRightPairProjection, correspondenceMiddlePair,
      correspondenceSixfoldSecondMiddlePair, correspondenceAmbientTarget, Category.assoc]

/-- The right ambient projection is flat by native base change of the first adjacent product. -/
instance flat_correspondenceSixfoldRightPairProjection [Flat f] [Flat g] :
    Flat (correspondenceSixfoldRightPairProjection f g h i) :=
  MorphismProperty.of_isPullback (correspondenceSixfold_right_isPullback f g h i) inferInstance

/-- The existing Z-first ambient is the actual base change of the last-pair diagonal. -/
theorem correspondenceSecondAmbient_baseChange_right :
    IsPullback (correspondenceSecondAmbientRightPairProjection f g h i)
      (correspondenceSecondAmbientInclusion f g h i)
      (correspondenceTripleInclusion g h i)
      (correspondenceSixfoldRightPairProjection f g h i) := by
  have hp : IsPullback (correspondenceSecondAmbientRightPairProjection f g h i)
      (correspondenceSecondAmbientInclusion f g h i ≫
        correspondenceSixfoldFirstFactorProjection f g h i)
      (correspondenceTripleInclusion g h i ≫ (correspondenceAmbientSource g h i ≫ g))
      (pullback.snd f g ≫ g) := by
    simpa only [correspondenceSecondAmbientInclusion_firstFactor,
      correspondenceAmbientSource, correspondenceTripleSource, Category.assoc,
      correspondenceTripleInclusion_fst_assoc] using
      (correspondenceSecondAmbient_right_isPullback f g h i).flip
  exact (hp.of_bot (correspondenceSecondAmbientInclusion_rightPair f g h i).symm
    (correspondenceSixfold_right_isPullback f g h i).flip)

variable (x : correspondenceTripleIncidence f g h i z w v)

local notation3 (prettyPrint := false) "u" =>
  correspondenceTripleIncidenceToRightSupportProduct f g h i z w v x
local notation3 (prettyPrint := false) "π" =>
  correspondenceRightExteriorProjection f g h i z w v
local notation3 (prettyPrint := false) "p" =>
  correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x
local notation3 (prettyPrint := false) "p₀" =>
  correspondenceIncidenceAmbientInclusion g h i w v (π u)
local notation3 (prettyPrint := false) "e" =>
  correspondenceRightIntermediateToTripleSupport f g h i z w v u
local notation3 (prettyPrint := false) "e₀" =>
  correspondenceIncidenceToSupportProduct g h i w v (π u)
local notation3 (prettyPrint := false) "A" =>
  correspondenceTripleIncidenceAmbientStalk f g h i z w v x
local notation3 (prettyPrint := false) "A₀" => correspondenceIncidenceAmbientStalk g h i w v (π u)
local notation3 (prettyPrint := false) "D" =>
  (correspondenceTripleSupportProduct f g h i z w v).presheaf.stalk e

/-- Reassociation gives equal actual support points, not a new coefficient model. -/
theorem correspondenceTripleIncidence_rightSupport_point_eq :
    correspondenceTripleIncidenceToTripleSupport f g h i z w v x = e :=
  (congrArg (fun m => m x)
    (correspondenceTripleIncidenceToRightSupportProduct_support f g h i z w v)).symm

/-- The common sixfold point is the actual image of the right-labelled support point. -/
theorem correspondenceTripleIncidence_rightSupport_ambient_point_eq :
    p = correspondenceTripleSupportProductInclusion f g h i z w v e :=
  (correspondenceTripleIncidence_ambient_point_eq f g h i z w v x).trans
    (congrArg (correspondenceTripleSupportProductInclusion f g h i z w v)
      (correspondenceTripleIncidence_rightSupport_point_eq f g h i z w v x))

/-- The pair-incidence ambient point is the actual projection of the sixfold ambient point. -/
theorem correspondenceTripleIncidence_rightPairAmbient_point_eq :
    p₀ = correspondenceSixfoldRightPairProjection f g h i p := by
  have he := congrArg (fun m => m u)
    (correspondenceRightIntermediateAmbientInclusion_pairProjection f g h i z w v)
  simp only [Scheme.Hom.comp_apply] at he
  exact he.symm.trans (congrArg (correspondenceSixfoldRightPairProjection f g h i)
    (correspondenceTripleIncidence_rightFirstStage_point_eq f g h i z w v x).symm)

/-- The actual original-pair-to-sixfold ambient stalk map with its proved point transport. -/
def correspondenceTripleIncidenceRightPairAmbientStalkMap : A₀ →+* A :=
  (((correspondenceIntersectionAmbient g h i).presheaf.stalkCongr
    (Inseparable.of_eq (correspondenceTripleIncidence_rightPairAmbient_point_eq f g h i z w v
      x))).hom ≫
      (correspondenceSixfoldRightPairProjection f g h i).stalkMap p).hom

/-- The actual pair ambient scalar map is flat, without a flatness condition on a support. -/
theorem flat_correspondenceTripleIncidenceRightPairAmbientStalkMap [Flat f] [Flat g] :
    (correspondenceTripleIncidenceRightPairAmbientStalkMap f g h i z w v x).Flat := by
  apply RingHom.Flat.comp
  · exact RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
  · exact Flat.stalkMap (correspondenceSixfoldRightPairProjection f g h i) p

/-- The original Z self-product point is the actual common second-middle point. -/
theorem correspondenceTripleIncidence_originalSecondMiddle_point_eq :
    correspondenceMiddlePair g h i p₀ = correspondenceSixfoldSecondMiddlePair f g h i p := by
  have hp := congrArg (correspondenceMiddlePair g h i)
    (correspondenceTripleIncidence_rightPairAmbient_point_eq f g h i z w v x)
  exact hp.trans (congrArg (fun m => m p)
    (correspondenceSixfoldRightPairProjection_middlePair f g h i))

/-- Pulling the original Z family through the pair ambient is literally its native sixfold
middle-stalk pullback, with only the proved equality of original Z points transported. -/
theorem correspondenceTripleIncidence_originalSecondMiddle_stalkMap :
    (correspondenceTripleIncidenceRightPairAmbientStalkMap f g h i z w v x).comp
        ((correspondenceMiddlePair g h i).stalkMap p₀).hom =
      (((pullback h h).presheaf.stalkCongr
        (Inseparable.of_eq
          (correspondenceTripleIncidence_originalSecondMiddle_point_eq f g h i z w v x))).hom ≫
            (correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom := by
  have hc := transported_stalkMap_comp (correspondenceSixfoldRightPairProjection f g h i)
    (correspondenceMiddlePair g h i) p p₀ (correspondenceMiddlePair g h i p₀)
    (correspondenceTripleIncidence_rightPairAmbient_point_eq f g h i z w v x) rfl
  change (((correspondenceMiddlePair g h i).stalkMap p₀) ≫
    (((correspondenceIntersectionAmbient g h i).presheaf.stalkCongr
      (Inseparable.of_eq
        (correspondenceTripleIncidence_rightPairAmbient_point_eq f g h i z w v x))).hom ≫
          (correspondenceSixfoldRightPairProjection f g h i).stalkMap p)).hom = _
  have hfinal := transported_stalkMap_congr
    (correspondenceSixfoldRightPairProjection f g h i ≫ correspondenceMiddlePair g h i)
    (correspondenceSixfoldSecondMiddlePair f g h i)
    (correspondenceSixfoldRightPairProjection_middlePair f g h i) p
    (correspondenceMiddlePair g h i p₀)
    (congrArg (correspondenceMiddlePair g h i)
      (correspondenceTripleIncidence_rightPairAmbient_point_eq f g h i z w v x))
    (correspondenceTripleIncidence_originalSecondMiddle_point_eq f g h i z w v x)
  have hcat := hc.trans hfinal
  simpa only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp] using congrArg (fun a => a.hom) hcat

/-- The actual full-exterior coefficient scalar map used in the sixfold Tor module. -/
def correspondenceTripleIncidenceRightSupportStalkMap : A →+* D :=
  (((correspondenceSixfoldAmbient f g h i).presheaf.stalkCongr
    (Inseparable.of_eq (correspondenceTripleIncidence_rightSupport_ambient_point_eq f g h i z w v
      x))).hom ≫
      (correspondenceTripleSupportProductInclusion f g h i z w v).stalkMap e).hom

/-- The original common coefficient module is transported to the actual right-labelled
support stalk. This uses the proved equality of support points, without replacing the module. -/
def correspondenceTripleIncidenceRightSupportStalkIso :
    correspondenceTripleIncidenceSupportStalkModule f g h i z w v x ≅
      (ModuleCat.restrictScalars
        (correspondenceTripleIncidenceRightSupportStalkMap f g h i z w v x)).obj
          (ModuleCat.of D D) := by
  let transport {X Y : Scheme.{u}} (j : Y ⟶ X)
      (p : X) (y y' : Y) (hy : p = j y) (hy' : p = j y') (h : y = y') :
      (ModuleCat.restrictScalars
        (((X.presheaf.stalkCongr (Inseparable.of_eq hy)).hom ≫ j.stalkMap y).hom)).obj
          (ModuleCat.of (Y.presheaf.stalk y) (Y.presheaf.stalk y)) ≅
      (ModuleCat.restrictScalars
        (((X.presheaf.stalkCongr (Inseparable.of_eq hy')).hom ≫ j.stalkMap y').hom)).obj
          (ModuleCat.of (Y.presheaf.stalk y') (Y.presheaf.stalk y')) := by
    subst y'
    exact Iso.refl _
  exact transport (correspondenceTripleSupportProductInclusion f g h i z w v)
    p (correspondenceTripleIncidenceToTripleSupport f g h i z w v x) e
    (correspondenceTripleIncidence_ambient_point_eq f g h i z w v x)
    (correspondenceTripleIncidence_rightSupport_ambient_point_eq f g h i z w v x)
    (correspondenceTripleIncidence_rightSupport_point_eq f g h i z w v x)

/-- The full-exterior coefficient map is the original surjective closed-immersion stalk map. -/
theorem correspondenceTripleIncidenceRightSupportStalkMap_surjective :
    Function.Surjective (correspondenceTripleIncidenceRightSupportStalkMap f g h i z w v x) :=
  (SurjectiveOnStalks.stalkMap_surjective
    (correspondenceTripleSupportProductInclusion f g h i z w v) e).comp
      (ConcreteCategory.bijective_of_isIso
        ((correspondenceSixfoldAmbient f g h i).presheaf.stalkCongr
          (Inseparable.of_eq
            (correspondenceTripleIncidence_rightSupport_ambient_point_eq f g h i z w v x))).hom).2

/-- Both actual routes from original pair ambient scalars to the full exterior stalk agree. -/
theorem correspondenceTripleIncidence_rightAmbientSupport_stalk_comm :
    (correspondenceTripleIncidenceRightSupportStalkMap f g h i z w v x).comp
        (correspondenceTripleIncidenceRightPairAmbientStalkMap f g h i z w v x) =
      (correspondenceRightExteriorSupportStalkMap f g h i z w v u).comp
        (correspondenceIncidenceSupportStalkMap g h i w v (π u)) := by
  change ((((correspondenceIntersectionAmbient g h i).presheaf.stalkCongr
    (Inseparable.of_eq (correspondenceTripleIncidence_rightPairAmbient_point_eq f g h i z w v
      x))).hom ≫
      (correspondenceSixfoldRightPairProjection f g h i).stalkMap p) ≫
      (((correspondenceSixfoldAmbient f g h i).presheaf.stalkCongr
        (Inseparable.of_eq (correspondenceTripleIncidence_rightSupport_ambient_point_eq f g h i z
          w v x))).hom ≫
          (correspondenceTripleSupportProductInclusion f g h i z w v).stalkMap e)).hom = _
  rw [transported_stalkMap_comp
    (correspondenceTripleSupportProductInclusion f g h i z w v)
    (correspondenceSixfoldRightPairProjection f g h i) e p p₀
    (correspondenceTripleIncidence_rightSupport_ambient_point_eq f g h i z w v x)
    (correspondenceTripleIncidence_rightPairAmbient_point_eq f g h i z w v x)]
  change _ = ((((correspondenceIntersectionAmbient g h i).presheaf.stalkCongr
    (Inseparable.of_eq (correspondenceIncidence_ambient_point_eq g h i w v (π u)))).hom ≫
      (correspondenceSupportProductInclusion g h i w v).stalkMap e₀) ≫
      (((correspondenceSupportProduct g h i w v).presheaf.stalkCongr
        (Inseparable.of_eq
          (correspondenceRightIntermediate_support_point_eq f g h i z w v u))).hom ≫
            (correspondenceTripleSupportRightProjection f g h i z w v).stalkMap e)).hom
  rw [transported_stalkMap_comp
    (correspondenceTripleSupportRightProjection f g h i z w v)
    (correspondenceSupportProductInclusion g h i w v) e e₀ p₀
    (correspondenceRightIntermediate_support_point_eq f g h i z w v u)
    (correspondenceIncidence_ambient_point_eq g h i w v (π u))]
  have hf : p₀ = (correspondenceTripleSupportProductInclusion f g h i z w v ≫
      correspondenceSixfoldRightPairProjection f g h i) e := by
    simpa only [Scheme.Hom.comp_apply] using
      (correspondenceTripleIncidence_rightPairAmbient_point_eq f g h i z w v x).trans
        (congrArg (correspondenceSixfoldRightPairProjection f g h i)
          (correspondenceTripleIncidence_rightSupport_ambient_point_eq f g h i z w v x))
  have hg : p₀ = (correspondenceTripleSupportRightProjection f g h i z w v ≫
      correspondenceSupportProductInclusion g h i w v) e := by
    simpa only [Scheme.Hom.comp_apply] using
      (correspondenceIncidence_ambient_point_eq g h i w v (π u)).trans
        (congrArg (correspondenceSupportProductInclusion g h i w v)
          (correspondenceRightIntermediate_support_point_eq f g h i z w v u))
  exact congrArg (fun a : A₀ ⟶ D => a.hom)
    (transported_stalkMap_congr _ _
      (correspondenceTripleSupportProductInclusion_rightPair f g h i z w v) e p₀ hf hg)

/-- The same coefficient scalar map factors the actual first-stage quotient map. -/
theorem correspondenceTripleIncidenceRightSupportStalkMap_firstStage_comp :
    (((correspondenceRightIntermediateToTripleSupport f g h i z w v).stalkMap u).hom).comp
        (correspondenceTripleIncidenceRightSupportStalkMap f g h i z w v x) =
      correspondenceTripleIncidenceRightFirstStageStalkMap f g h i z w v x := by
  have he : e = correspondenceRightIntermediateToTripleSupport f g h i z w v u := rfl
  have hc := transported_stalkMap_comp
    (correspondenceRightIntermediateToTripleSupport f g h i z w v)
    (correspondenceTripleSupportProductInclusion f g h i z w v) u e p he
    (correspondenceTripleIncidence_rightSupport_ambient_point_eq f g h i z w v x)
  have heq := transported_stalkMap_congr
    (correspondenceRightIntermediateToTripleSupport f g h i z w v ≫
      correspondenceTripleSupportProductInclusion f g h i z w v)
    (correspondenceRightIntermediateAmbientInclusion f g h i z w v)
    (correspondenceRightIntermediate_ambient_comm f g h i z w v).symm u p
    ((correspondenceTripleIncidence_rightSupport_ambient_point_eq f g h i z w v x).trans
      (congrArg (correspondenceTripleSupportProductInclusion f g h i z w v) he))
    (correspondenceTripleIncidence_rightFirstStage_point_eq f g h i z w v x)
  have hcat := hc.trans heq
  have htransport :
      ((correspondenceTripleSupportProduct f g h i z w v).presheaf.stalkCongr
        (Inseparable.of_eq he)).hom =
      𝟙 ((correspondenceTripleSupportProduct f g h i z w v).presheaf.stalk
        (correspondenceRightIntermediateToTripleSupport f g h i z w v u)) := by
    change (correspondenceTripleSupportProduct f g h i z w v).presheaf.stalkSpecializes
      (specializes_refl (correspondenceRightIntermediateToTripleSupport f g h i z w v u)) = _
    exact TopCat.Presheaf.stalkSpecializes_refl _ _
  rw [htransport] at hcat
  erw [Category.id_comp] at hcat
  change ((((correspondenceSixfoldAmbient f g h i).presheaf.stalkCongr
    (Inseparable.of_eq (correspondenceTripleIncidence_rightSupport_ambient_point_eq f g h i z w v
      x))).hom ≫
      (correspondenceTripleSupportProductInclusion f g h i z w v).stalkMap e) ≫
        (correspondenceRightIntermediateToTripleSupport f g h i z w v).stalkMap u).hom =
    (((correspondenceSixfoldAmbient f g h i).presheaf.stalkCongr
      (Inseparable.of_eq
        (correspondenceTripleIncidence_rightFirstStage_point_eq f g h i z w v x))).hom ≫
          (correspondenceRightIntermediateAmbientInclusion f g h i z w v).stalkMap u).hom
  exact congrArg (fun a : A ⟶
    (correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk u => a.hom) hcat

end Stacks.Chow
