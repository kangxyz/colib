/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.FirstStageExteriorBaseChange
public import Colib.AlgebraicGeometry.Correspondences.Composition.PairOriginalKoszulTor
public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleFirstStageAction

/-!
# Actual ambient and support scalar maps for the original first-stage coefficient

The original pair ambient stalk, sixfold ambient stalk, original pair support stalk, and
full exterior support stalk form a commuting square with their actual transported stalk
maps. The point comparisons come from the original first-stage and support projections.
The sixfold-to-support scalar map also factors the actual first-stage quotient map.

These are the map equations required to compare the literal original Y list in the two
coefficient complexes and then extend linearity to the full first-stage local ring. The
private equality-transport calculations only apply native stalk-map composition after
substituting equal points. No new ring, tensor model, or assumed map comparison is used.
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

/-- The native projection from the sixfold ambient to the original pair ambient. -/
abbrev correspondenceSixfoldPairProjection :
    correspondenceSixfoldAmbient f g h i ⟶ correspondenceIntersectionAmbient f g h :=
  pullback.fst (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h)

/-- The actual first-stage inclusion commutes with the original pair ambient projection. -/
@[reassoc]
theorem correspondenceLeftIntermediateAmbientInclusion_pairProjection :
    correspondenceLeftIntermediateAmbientInclusion f g h i z w v ≫
      correspondenceSixfoldPairProjection f g h i =
    pullback.fst (correspondenceIncidenceRight f g h z w ≫ h)
      (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h) ≫
        correspondenceIncidenceAmbientInclusion f g h z w := by
  simp only [correspondenceLeftIntermediateAmbientInclusion,
    correspondenceSixfoldPairProjection, Category.assoc,
    correspondenceFirstDiagonalInclusion_fst,
    correspondenceLeftIntermediateSupportInclusion_fst_assoc]

variable (x : correspondenceTripleIncidence f g h i z w v)

local notation3 (prettyPrint := false) "u" =>
  correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v x
local notation3 (prettyPrint := false) "π" =>
  (pullback.fst (correspondenceIncidenceRight f g h z w ≫ h)
    (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h) :
    correspondenceLeftIntermediateSupportProduct f g h i z w v ⟶
      correspondenceIncidence f g h z w)
local notation3 (prettyPrint := false) "p" =>
  correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x
local notation3 (prettyPrint := false) "p₀" =>
  correspondenceIncidenceAmbientInclusion f g h z w (π u)
local notation3 (prettyPrint := false) "e" =>
  correspondenceTripleIncidenceToTripleSupport f g h i z w v x
local notation3 (prettyPrint := false) "e₀" =>
  correspondenceIncidenceToSupportProduct f g h z w (π u)
local notation3 (prettyPrint := false) "A" =>
  correspondenceTripleIncidenceAmbientStalk f g h i z w v x
local notation3 (prettyPrint := false) "A₀" => correspondenceIncidenceAmbientStalk f g h z w (π u)
local notation3 (prettyPrint := false) "D" =>
  (correspondenceTripleSupportProduct f g h i z w v).presheaf.stalk e

/-- The pair-incidence ambient point is the actual projection of the sixfold ambient point. -/
theorem correspondenceTripleIncidence_pairAmbient_point_eq :
    p₀ = correspondenceSixfoldPairProjection f g h i p := by
  have he := congrArg (fun m => m u)
    (correspondenceLeftIntermediateAmbientInclusion_pairProjection f g h i z w v)
  simp only [Scheme.Hom.comp_apply] at he
  exact he.symm.trans (congrArg (correspondenceSixfoldPairProjection f g h i)
    (correspondenceTripleIncidence_firstStage_point_eq f g h i z w v x).symm)

/-- The actual original-pair-to-sixfold ambient stalk map with its proved point transport. -/
def correspondenceTripleIncidencePairAmbientStalkMap : A₀ →+* A :=
  (((correspondenceIntersectionAmbient f g h).presheaf.stalkCongr
    (Inseparable.of_eq (correspondenceTripleIncidence_pairAmbient_point_eq f g h i z w v x))).hom ≫
      (correspondenceSixfoldPairProjection f g h i).stalkMap p).hom

/-- The actual pair ambient scalar map is flat, without a flatness condition on a support. -/
theorem flat_correspondenceTripleIncidencePairAmbientStalkMap [Flat h] [Flat i] :
    (correspondenceTripleIncidencePairAmbientStalkMap f g h i z w v x).Flat := by
  have : Flat (correspondenceSixfoldPairProjection f g h i) := by
    dsimp only [correspondenceSixfoldPairProjection]
    infer_instance
  apply RingHom.Flat.comp
  · exact RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
  · exact Flat.stalkMap (correspondenceSixfoldPairProjection f g h i) p

/-- The original Y self-product point is the same point under the actual sixfold projection. -/
theorem correspondenceTripleIncidence_originalMiddle_point_eq :
    correspondenceMiddlePair f g h p₀ = correspondenceSixfoldFirstMiddlePair f g h i p :=
  congrArg (correspondenceMiddlePair f g h)
    (correspondenceTripleIncidence_pairAmbient_point_eq f g h i z w v x)

/-- Pulling the original Y family through the pair ambient is literally its native sixfold
middle-stalk pullback, with only the proved equality of original Y points transported. -/
theorem correspondenceTripleIncidence_originalMiddle_stalkMap :
    (correspondenceTripleIncidencePairAmbientStalkMap f g h i z w v x).comp
        ((correspondenceMiddlePair f g h).stalkMap p₀).hom =
      (((pullback g g).presheaf.stalkCongr
        (Inseparable.of_eq
          (correspondenceTripleIncidence_originalMiddle_point_eq f g h i z w v x))).hom ≫
            (correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom := by
  have hc := transported_stalkMap_comp (correspondenceSixfoldPairProjection f g h i)
    (correspondenceMiddlePair f g h) p p₀ (correspondenceMiddlePair f g h p₀)
    (correspondenceTripleIncidence_pairAmbient_point_eq f g h i z w v x) rfl
  change (((correspondenceMiddlePair f g h).stalkMap p₀) ≫
    (((correspondenceIntersectionAmbient f g h).presheaf.stalkCongr
      (Inseparable.of_eq
        (correspondenceTripleIncidence_pairAmbient_point_eq f g h i z w v x))).hom ≫
          (correspondenceSixfoldPairProjection f g h i).stalkMap p)).hom = _
  simpa only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp] using congrArg (fun a => a.hom) hc

/-- The actual full-exterior coefficient scalar map used in the sixfold Tor module. -/
def correspondenceTripleIncidenceSupportStalkMap : A →+* D :=
  (((correspondenceSixfoldAmbient f g h i).presheaf.stalkCongr
    (Inseparable.of_eq (correspondenceTripleIncidence_ambient_point_eq f g h i z w v x))).hom ≫
      (correspondenceTripleSupportProductInclusion f g h i z w v).stalkMap e).hom

/-- The full-exterior coefficient map is the original surjective closed-immersion stalk map. -/
theorem correspondenceTripleIncidenceSupportStalkMap_surjective :
    Function.Surjective (correspondenceTripleIncidenceSupportStalkMap f g h i z w v x) :=
  (SurjectiveOnStalks.stalkMap_surjective
    (correspondenceTripleSupportProductInclusion f g h i z w v) e).comp
      (ConcreteCategory.bijective_of_isIso
        ((correspondenceSixfoldAmbient f g h i).presheaf.stalkCongr
          (Inseparable.of_eq
            (correspondenceTripleIncidence_ambient_point_eq f g h i z w v x))).hom).2

/-- Both actual routes from original pair ambient scalars to the full exterior stalk agree. -/
theorem correspondenceTripleIncidence_ambientSupport_stalk_comm :
    (correspondenceTripleIncidenceSupportStalkMap f g h i z w v x).comp
        (correspondenceTripleIncidencePairAmbientStalkMap f g h i z w v x) =
      (correspondenceLeftExteriorSupportStalkMap f g h i z w v u).comp
        (correspondenceIncidenceSupportStalkMap f g h z w (π u)) := by
  change ((((correspondenceIntersectionAmbient f g h).presheaf.stalkCongr
    (Inseparable.of_eq (correspondenceTripleIncidence_pairAmbient_point_eq f g h i z w v x))).hom ≫
      (correspondenceSixfoldPairProjection f g h i).stalkMap p) ≫
      (((correspondenceSixfoldAmbient f g h i).presheaf.stalkCongr
        (Inseparable.of_eq (correspondenceTripleIncidence_ambient_point_eq f g h i z w v x))).hom ≫
          (correspondenceTripleSupportProductInclusion f g h i z w v).stalkMap e)).hom = _
  rw [transported_stalkMap_comp
    (correspondenceTripleSupportProductInclusion f g h i z w v)
    (correspondenceSixfoldPairProjection f g h i) e p p₀
    (correspondenceTripleIncidence_ambient_point_eq f g h i z w v x)
    (correspondenceTripleIncidence_pairAmbient_point_eq f g h i z w v x)]
  change _ = ((((correspondenceIntersectionAmbient f g h).presheaf.stalkCongr
    (Inseparable.of_eq (correspondenceIncidence_ambient_point_eq f g h z w (π u)))).hom ≫
      (correspondenceSupportProductInclusion f g h z w).stalkMap e₀) ≫
      (((correspondenceSupportProduct f g h z w).presheaf.stalkCongr
        (Inseparable.of_eq
          (correspondenceLeftIntermediate_support_point_eq f g h i z w v u))).hom ≫
            (correspondenceTripleSupportProjection f g h i z w v).stalkMap e)).hom
  rw [transported_stalkMap_comp
    (correspondenceTripleSupportProjection f g h i z w v)
    (correspondenceSupportProductInclusion f g h z w) e e₀ p₀
    (correspondenceLeftIntermediate_support_point_eq f g h i z w v u)
    (correspondenceIncidence_ambient_point_eq f g h z w (π u))]
  have hf : p₀ = (correspondenceTripleSupportProductInclusion f g h i z w v ≫
      correspondenceSixfoldPairProjection f g h i) e := by
    simpa only [Scheme.Hom.comp_apply] using
      (correspondenceTripleIncidence_pairAmbient_point_eq f g h i z w v x).trans
        (congrArg (correspondenceSixfoldPairProjection f g h i)
          (correspondenceTripleIncidence_ambient_point_eq f g h i z w v x))
  have hg : p₀ = (correspondenceTripleSupportProjection f g h i z w v ≫
      correspondenceSupportProductInclusion f g h z w) e := by
    simpa only [Scheme.Hom.comp_apply] using
      (correspondenceIncidence_ambient_point_eq f g h z w (π u)).trans
        (congrArg (correspondenceSupportProductInclusion f g h z w)
          (correspondenceLeftIntermediate_support_point_eq f g h i z w v u))
  exact congrArg (fun a : A₀ ⟶ D => a.hom)
    (transported_stalkMap_congr _ _
      (correspondenceTripleSupportProductInclusion_fst f g h i z w v) e p₀ hf hg)

/-- The same coefficient scalar map factors the actual first-stage quotient map. -/
theorem correspondenceTripleIncidenceSupportStalkMap_firstStage_comp :
    (((correspondenceLeftIntermediateToTripleSupport f g h i z w v).stalkMap u).hom).comp
        (correspondenceTripleIncidenceSupportStalkMap f g h i z w v x) =
      correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v x := by
  have he : e = correspondenceLeftIntermediateToTripleSupport f g h i z w v u := rfl
  have hc := transported_stalkMap_comp
    (correspondenceLeftIntermediateToTripleSupport f g h i z w v)
    (correspondenceTripleSupportProductInclusion f g h i z w v) u e p he
    (correspondenceTripleIncidence_ambient_point_eq f g h i z w v x)
  have heq := transported_stalkMap_congr
    (correspondenceLeftIntermediateToTripleSupport f g h i z w v ≫
      correspondenceTripleSupportProductInclusion f g h i z w v)
    (correspondenceLeftIntermediateAmbientInclusion f g h i z w v)
    (correspondenceLeftIntermediate_ambient_comm f g h i z w v).symm u p
    ((correspondenceTripleIncidence_ambient_point_eq f g h i z w v x).trans
      (congrArg (correspondenceTripleSupportProductInclusion f g h i z w v) he))
    (correspondenceTripleIncidence_firstStage_point_eq f g h i z w v x)
  have hcat := hc.trans heq
  have htransport :
      ((correspondenceTripleSupportProduct f g h i z w v).presheaf.stalkCongr
        (Inseparable.of_eq he)).hom =
      𝟙 ((correspondenceTripleSupportProduct f g h i z w v).presheaf.stalk
        (correspondenceLeftIntermediateToTripleSupport f g h i z w v u)) := by
    change (correspondenceTripleSupportProduct f g h i z w v).presheaf.stalkSpecializes
      (specializes_refl (correspondenceLeftIntermediateToTripleSupport f g h i z w v u)) = _
    exact TopCat.Presheaf.stalkSpecializes_refl _ _
  rw [htransport, Category.id_comp] at hcat
  change ((((correspondenceSixfoldAmbient f g h i).presheaf.stalkCongr
    (Inseparable.of_eq (correspondenceTripleIncidence_ambient_point_eq f g h i z w v x))).hom ≫
      (correspondenceTripleSupportProductInclusion f g h i z w v).stalkMap e) ≫
        (correspondenceLeftIntermediateToTripleSupport f g h i z w v).stalkMap u).hom =
    (((correspondenceSixfoldAmbient f g h i).presheaf.stalkCongr
      (Inseparable.of_eq
        (correspondenceTripleIncidence_firstStage_point_eq f g h i z w v x))).hom ≫
          (correspondenceLeftIntermediateAmbientInclusion f g h i z w v).stalkMap u).hom
  exact congrArg (fun a : A ⟶
    (correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk u => a.hom) hcat

end Stacks.Chow
