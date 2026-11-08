/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingImage
public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleStalkModules

/-!
# The actual Z-first support intersection in the common sixfold ambient

The existing second-diagonal ambient imposes Z first. Its intersection with the
unchanged three-support product is the actual right exterior F times incidence(G,H).
The three right-coordinate pullback squares below are the native pullback associativity
construction. They reorder parentheses, not the supports or the direction of admissibility.
Their actual maps provide the kernel sum and scalar square for right first-stage homology.

The reference target is motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
Composition/Cycles/RightFirstStageWeightedRemainingCoefficient.lean. Only its actual
Z-first geometry is supplied here; no weighted-cycle comparison is an assumption.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The original source coordinate of a four-factor pair ambient. -/
abbrev correspondenceAmbientSource : correspondenceIntersectionAmbient f g h ⟶ X :=
  pullback.fst _ _ ≫ pullback.fst f g

/-- The original source coordinate after the pair diagonal. -/
abbrev correspondenceTripleSource : correspondenceTripleProduct f g h ⟶ X :=
  pullback.fst _ _ ≫ pullback.fst f g

/-- The original source coordinate of the full pair-support product. -/
abbrev correspondenceSupportProductSource : correspondenceSupportProduct f g h z w ⟶ X :=
  pullback.fst _ _ ≫ (integralComponentAt z).subschemeι ≫ pullback.fst f g

/-- The first adjacent product in the unchanged sixfold ambient. -/
abbrev correspondenceSixfoldFirstFactorProjection :
    correspondenceSixfoldAmbient f g h i ⟶ pullback f g :=
  pullback.fst _ _ ≫ pullback.fst _ _

/-- The last two adjacent products, grouped by the native pullback construction. -/
def correspondenceSixfoldRightPairProjection :
    correspondenceSixfoldAmbient f g h i ⟶ correspondenceIntersectionAmbient g h i :=
  pullback.lift (pullback.fst _ _ ≫ pullback.snd _ _) (pullback.snd _ _)
    (by simpa only [correspondenceAmbientTarget, Category.assoc] using
      (pullback.condition (f := correspondenceAmbientTarget f g h ≫ h)
        (g := pullback.fst h i ≫ h)))

/-- The common ambient is the actual right-associated product, by native associativity. -/
theorem correspondenceSixfold_right_isPullback :
    IsPullback (correspondenceSixfoldFirstFactorProjection f g h i)
      (correspondenceSixfoldRightPairProjection f g h i)
      (pullback.snd f g ≫ g) (correspondenceAmbientSource g h i ≫ g) := by
  let a := pullback.snd f g ≫ g
  let b := pullback.fst g h ≫ g
  let c := pullback.snd g h ≫ h
  let d := pullback.fst h i ≫ h
  let e₀ : correspondenceSixfoldAmbient f g h i ≅
      pullback (pullback.snd a b ≫ c) d :=
    pullback.congrHom (by simp only [correspondenceAmbientTarget, a, b, c, Category.assoc]) rfl
  let e₁ := pullbackAssoc a b c d
  let e₂ : pullback a (pullback.fst c d ≫ b) ≅
      pullback a (correspondenceAmbientSource g h i ≫ g) :=
    pullback.congrHom rfl (by simp only [correspondenceAmbientSource, b, c, d, Category.assoc])
  let e := e₀ ≪≫ e₁ ≪≫ e₂
  refine (IsPullback.of_hasPullback a (correspondenceAmbientSource g h i ≫ g)).of_iso'
    e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp [a]) (by simp)
  · simp [a, b, c, d, e, e₀, e₁, e₂, correspondenceSixfoldFirstFactorProjection,
      pullback.congrHom_hom, pullback.map, Category.assoc]
  · apply pullback.hom_ext <;>
      simp [a, b, c, d, e, e₀, e₁, e₂, correspondenceSixfoldRightPairProjection,
        pullback.congrHom_hom, pullback.map, Category.assoc]

/-- The first adjacent product after imposing Z first. -/
abbrev correspondenceSecondAmbientFirstFactorProjection :
    correspondenceSecondDiagonalAmbient f g h i ⟶ pullback f g :=
  pullback.fst _ _ ≫ pullback.fst _ _

/-- The original last-pair triple product after imposing Z first. -/
def correspondenceSecondAmbientRightPairProjection :
    correspondenceSecondDiagonalAmbient f g h i ⟶ correspondenceTripleProduct g h i :=
  pullback.lift (pullback.fst _ _ ≫ pullback.snd _ _) (pullback.snd _ _)
    (by simpa only [correspondenceAmbientTarget, Category.assoc] using
      (pullback.condition (f := correspondenceAmbientTarget f g h)
        (g := pullback.fst h i)))

/-- Native associativity identifies the genuine Z-first ambient as the right product. -/
theorem correspondenceSecondAmbient_right_isPullback :
    IsPullback (correspondenceSecondAmbientFirstFactorProjection f g h i)
      (correspondenceSecondAmbientRightPairProjection f g h i)
      (pullback.snd f g ≫ g) (correspondenceTripleSource g h i ≫ g) := by
  let a := pullback.snd f g ≫ g
  let b := pullback.fst g h ≫ g
  let c := pullback.snd g h
  let d := pullback.fst h i
  let e₁ : correspondenceSecondDiagonalAmbient f g h i ≅
      pullback a (pullback.fst c d ≫ b) := pullbackAssoc a b c d
  let e₂ : pullback a (pullback.fst c d ≫ b) ≅
      pullback a (correspondenceTripleSource g h i ≫ g) :=
    pullback.congrHom rfl (by simp only [correspondenceTripleSource, b, c, d, Category.assoc])
  let e := e₁ ≪≫ e₂
  refine (IsPullback.of_hasPullback a (correspondenceTripleSource g h i ≫ g)).of_iso'
    e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp [a]) (by simp)
  · simp [a, b, c, d, e, e₁, e₂, correspondenceSecondAmbientFirstFactorProjection,
      pullback.congrHom_hom, pullback.map, Category.assoc]
  · apply pullback.hom_ext <;>
      simp [a, b, c, d, e, e₁, e₂, correspondenceSecondAmbientRightPairProjection,
        pullback.congrHom_hom, pullback.map, Category.assoc]

/-- The common coefficient support's original first support coordinate. -/
abbrev correspondenceTripleSupportFirstProjection :
    correspondenceTripleSupportProduct f g h i z w v ⟶ (integralComponentAt z).subscheme :=
  pullback.fst _ _ ≫ pullback.fst _ _

/-- The common coefficient support's actual last two support factors. -/
def correspondenceTripleSupportRightProjection :
    correspondenceTripleSupportProduct f g h i z w v ⟶ correspondenceSupportProduct g h i w v :=
  pullback.lift (pullback.fst _ _ ≫ pullback.snd _ _) (pullback.snd _ _)
    (by simpa only [correspondenceSupportProductTarget, Category.assoc] using
      (pullback.condition (f := correspondenceSupportProductTarget f g h z w ≫ h)
        (g := ((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)))

/-- Native associativity retains the actual full three-support scheme. -/
theorem correspondenceTripleSupport_right_isPullback :
    IsPullback (correspondenceTripleSupportFirstProjection f g h i z w v)
      (correspondenceTripleSupportRightProjection f g h i z w v)
      (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g)
      (correspondenceSupportProductSource g h i w v ≫ g) := by
  let a := (integralComponentAt z).subschemeι ≫ pullback.snd f g ≫ g
  let b := (integralComponentAt w).subschemeι ≫ pullback.fst g h ≫ g
  let c := (integralComponentAt w).subschemeι ≫ pullback.snd g h ≫ h
  let d := (integralComponentAt v).subschemeι ≫ pullback.fst h i ≫ h
  let e₀ : correspondenceTripleSupportProduct f g h i z w v ≅
      pullback (pullback.snd a b ≫ c) d :=
    pullback.congrHom
      (by simp only [correspondenceSupportProductTarget, a, b, c, Category.assoc])
      (by simp only [d, Category.assoc])
  let e₁ := pullbackAssoc a b c d
  let e₂ : pullback a (pullback.fst c d ≫ b) ≅
      pullback (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g)
        (correspondenceSupportProductSource g h i w v ≫ g) :=
    pullback.congrHom (by simp only [a, Category.assoc])
      (by simp only [correspondenceSupportProductSource, b, c, d, Category.assoc])
  let e := e₀ ≪≫ e₁ ≪≫ e₂
  refine (IsPullback.of_hasPullback
    (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g)
    (correspondenceSupportProductSource g h i w v ≫ g)).of_iso'
    e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · simp [a, b, c, d, e, e₀, e₁, e₂, correspondenceTripleSupportFirstProjection,
      pullback.congrHom_hom, pullback.map, Category.assoc]
  · apply pullback.hom_ext <;>
      simp [a, b, c, d, e, e₀, e₁, e₂, correspondenceTripleSupportRightProjection,
        pullback.congrHom_hom, pullback.map, Category.assoc]

/-- Z-first inclusion retains the first factor. -/
@[reassoc (attr := simp)]
theorem correspondenceSecondAmbientInclusion_firstFactor :
    correspondenceSecondAmbientInclusion f g h i ≫
        correspondenceSixfoldFirstFactorProjection f g h i =
      correspondenceSecondAmbientFirstFactorProjection f g h i := by
  simp [correspondenceSixfoldFirstFactorProjection,
    correspondenceSecondAmbientFirstFactorProjection]

/-- Z-first inclusion retains the actual last-pair diagonal inclusion. -/
@[reassoc (attr := simp)]
theorem correspondenceSecondAmbientInclusion_rightPair :
    correspondenceSecondAmbientInclusion f g h i ≫
        correspondenceSixfoldRightPairProjection f g h i =
      correspondenceSecondAmbientRightPairProjection f g h i ≫
        correspondenceTripleInclusion g h i := by
  apply pullback.hom_ext <;>
    simp [correspondenceSixfoldRightPairProjection,
      correspondenceSecondAmbientRightPairProjection, Category.assoc]

/-- The unchanged full support inclusion retains its first actual support. -/
@[reassoc (attr := simp)]
theorem correspondenceTripleSupportProductInclusion_firstFactor :
    correspondenceTripleSupportProductInclusion f g h i z w v ≫
        correspondenceSixfoldFirstFactorProjection f g h i =
      correspondenceTripleSupportFirstProjection f g h i z w v ≫
        (integralComponentAt z).subschemeι := by
  simp [correspondenceSixfoldFirstFactorProjection,
    correspondenceTripleSupportFirstProjection, Category.assoc]

/-- The unchanged full support inclusion retains the last two support inclusions. -/
@[reassoc (attr := simp)]
theorem correspondenceTripleSupportProductInclusion_rightPair :
    correspondenceTripleSupportProductInclusion f g h i z w v ≫
        correspondenceSixfoldRightPairProjection f g h i =
      correspondenceTripleSupportRightProjection f g h i z w v ≫
        correspondenceSupportProductInclusion g h i w v := by
  apply pullback.hom_ext <;>
    simp [correspondenceSixfoldRightPairProjection,
      correspondenceTripleSupportRightProjection, Category.assoc]

/-- The right-stage support embeds in the existing Z-first ambient. -/
def correspondenceRightIntermediateSupportInclusion :
    correspondenceRightIntermediateSupportProduct f g h i z w v ⟶
      correspondenceSecondDiagonalAmbient f g h i :=
  pullback.map _ _ _ _ (integralComponentAt z).subschemeι
    (correspondenceIncidenceInclusion g h i w v) (𝟙 S)
      (by simp) (by simp [correspondenceTripleSource, correspondenceIncidenceLeft]) ≫
    (correspondenceSecondAmbient_right_isPullback f g h i).isoPullback.inv

/-- The right-stage support maps to the original common full coefficient support. -/
def correspondenceRightIntermediateToTripleSupport :
    correspondenceRightIntermediateSupportProduct f g h i z w v ⟶
      correspondenceTripleSupportProduct f g h i z w v :=
  pullback.map _ _ _ _ (𝟙 (integralComponentAt z).subscheme)
    (correspondenceIncidenceToSupportProduct g h i w v) (𝟙 S)
      (by simp) (by simp [correspondenceSupportProductSource, correspondenceIncidenceLeft]) ≫
    (correspondenceTripleSupport_right_isPullback f g h i z w v).isoPullback.inv

instance isClosedImmersion_correspondenceRightIntermediateSupportInclusion :
    IsClosedImmersion (correspondenceRightIntermediateSupportInclusion f g h i z w v) := by
  unfold correspondenceRightIntermediateSupportInclusion
  let : IsClosedImmersion (pullback.map
      (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g)
      (correspondenceIncidenceLeft g h i w v ≫ g)
      (pullback.snd f g ≫ g) (correspondenceTripleSource g h i ≫ g)
      (integralComponentAt z).subschemeι (correspondenceIncidenceInclusion g h i w v) (𝟙 S)
      (by simp) (by simp [correspondenceTripleSource, correspondenceIncidenceLeft])) :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion)
      inferInstance inferInstance (by simp)
      (by simp [correspondenceTripleSource, correspondenceIncidenceLeft])
  infer_instance

@[reassoc (attr := simp)]
theorem correspondenceRightIntermediateSupportInclusion_firstFactor :
    correspondenceRightIntermediateSupportInclusion f g h i z w v ≫
        correspondenceSecondAmbientFirstFactorProjection f g h i =
      pullback.fst _ _ ≫ (integralComponentAt z).subschemeι := by
  simp [correspondenceRightIntermediateSupportInclusion, Category.assoc]

@[reassoc (attr := simp)]
theorem correspondenceRightIntermediateSupportInclusion_rightPair :
    correspondenceRightIntermediateSupportInclusion f g h i z w v ≫
        correspondenceSecondAmbientRightPairProjection f g h i =
      correspondenceRightExteriorProjection f g h i z w v ≫
        correspondenceIncidenceInclusion g h i w v := by
  simp [correspondenceRightIntermediateSupportInclusion,
    correspondenceRightExteriorProjection, Category.assoc]

@[reassoc (attr := simp)]
theorem correspondenceRightIntermediateToTripleSupport_firstFactor :
    correspondenceRightIntermediateToTripleSupport f g h i z w v ≫
        correspondenceTripleSupportFirstProjection f g h i z w v = pullback.fst _ _ := by
  simp [correspondenceRightIntermediateToTripleSupport, Category.assoc]

@[reassoc (attr := simp)]
theorem correspondenceRightIntermediateToTripleSupport_rightPair :
    correspondenceRightIntermediateToTripleSupport f g h i z w v ≫
        correspondenceTripleSupportRightProjection f g h i z w v =
      correspondenceRightExteriorProjection f g h i z w v ≫
        correspondenceIncidenceToSupportProduct g h i w v := by
  simp [correspondenceRightIntermediateToTripleSupport,
    correspondenceRightExteriorProjection, Category.assoc]

/-- Both right-stage maps give the same literal sixfold morphism. -/
@[reassoc]
theorem correspondenceRightIntermediate_ambient_comm :
    correspondenceRightIntermediateSupportInclusion f g h i z w v ≫
        correspondenceSecondAmbientInclusion f g h i =
      correspondenceRightIntermediateToTripleSupport f g h i z w v ≫
        correspondenceTripleSupportProductInclusion f g h i z w v := by
  apply (correspondenceSixfold_right_isPullback f g h i).hom_ext
  · simp
  · simp [Category.assoc, correspondenceIncidence_ambient_comm]

/-- The full right exterior is the actual intersection with the Z-first ambient. -/
theorem correspondenceRightIntermediate_ambient_isPullback :
    IsPullback (correspondenceRightIntermediateSupportInclusion f g h i z w v)
      (correspondenceRightIntermediateToTripleSupport f g h i z w v)
      (correspondenceSecondAmbientInclusion f g h i)
      (correspondenceTripleSupportProductInclusion f g h i z w v) where
  w := correspondenceRightIntermediate_ambient_comm f g h i z w v
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun c => by
    have hF := congrArg (fun m => m ≫ correspondenceSixfoldFirstFactorProjection f g h i)
      c.condition
    have hP := congrArg (fun m => m ≫ correspondenceSixfoldRightPairProjection f g h i)
      c.condition
    simp only [Category.assoc, correspondenceSecondAmbientInclusion_firstFactor,
      correspondenceTripleSupportProductInclusion_firstFactor] at hF
    simp only [Category.assoc, correspondenceSecondAmbientInclusion_rightPair,
      correspondenceTripleSupportProductInclusion_rightPair] at hP
    let pairLift := (isPullback_correspondenceAmbientIncidence g h i w v).lift
      (c.fst ≫ correspondenceSecondAmbientRightPairProjection f g h i)
      (c.snd ≫ correspondenceTripleSupportRightProjection f g h i z w v)
      (by simpa only [Category.assoc] using hP)
    have hp₁ : pairLift ≫ correspondenceIncidenceInclusion g h i w v =
        c.fst ≫ correspondenceSecondAmbientRightPairProjection f g h i :=
      IsPullback.lift_fst _ _ _ _
    have hp₂ : pairLift ≫ correspondenceIncidenceToSupportProduct g h i w v =
        c.snd ≫ correspondenceTripleSupportRightProjection f g h i z w v :=
      IsPullback.lift_snd _ _ _ _
    have hbase :
        (c.snd ≫ correspondenceTripleSupportFirstProjection f g h i z w v) ≫
          (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g) =
        pairLift ≫ (correspondenceIncidenceLeft g h i w v ≫ g) := by
      calc
        _ = (c.snd ≫ correspondenceTripleSupportRightProjection f g h i z w v) ≫
            (correspondenceSupportProductSource g h i w v ≫ g) := by
          simpa only [Category.assoc] using congrArg (c.snd ≫ ·)
            (correspondenceTripleSupport_right_isPullback f g h i z w v).w
        _ = (pairLift ≫ correspondenceIncidenceToSupportProduct g h i w v) ≫
            (correspondenceSupportProductSource g h i w v ≫ g) := by rw [hp₂]
        _ = _ := by
          simp [correspondenceSupportProductSource, correspondenceIncidenceLeft, Category.assoc]
    let e := pullback.lift
      (c.snd ≫ correspondenceTripleSupportFirstProjection f g h i z w v) pairLift hbase
    have he₁ : e ≫ correspondenceRightIntermediateSupportInclusion f g h i z w v = c.fst := by
      apply (correspondenceSecondAmbient_right_isPullback f g h i).hom_ext
      · simpa only [Category.assoc, correspondenceRightIntermediateSupportInclusion_firstFactor,
          e, pullback.lift_fst_assoc] using hF.symm
      · simpa only [Category.assoc, correspondenceRightIntermediateSupportInclusion_rightPair,
          e, correspondenceRightExteriorProjection, pullback.lift_snd_assoc] using hp₁
    have he₂ : e ≫ correspondenceRightIntermediateToTripleSupport f g h i z w v = c.snd := by
      apply (correspondenceTripleSupport_right_isPullback f g h i z w v).hom_ext
      · simp only [Category.assoc, correspondenceRightIntermediateToTripleSupport_firstFactor,
          e, pullback.lift_fst]
      · simpa only [Category.assoc, correspondenceRightIntermediateToTripleSupport_rightPair,
          e, correspondenceRightExteriorProjection, pullback.lift_snd_assoc] using hp₂
    refine ⟨e, he₁, he₂, ?_⟩
    intro m hm _
    exact (cancel_mono (correspondenceRightIntermediateSupportInclusion f g h i z w v)).mp
      (hm.trans he₁.symm))⟩

/-- The genuine right first-stage inclusion in the common ambient. -/
abbrev correspondenceRightIntermediateAmbientInclusion :
    correspondenceRightIntermediateSupportProduct f g h i z w v ⟶
      correspondenceSixfoldAmbient f g h i :=
  correspondenceRightIntermediateSupportInclusion f g h i z w v ≫
    correspondenceSecondAmbientInclusion f g h i

instance isClosedImmersion_correspondenceRightIntermediateAmbientInclusion [IsSeparated h] :
    IsClosedImmersion (correspondenceRightIntermediateAmbientInclusion f g h i z w v) := by
  dsimp only [correspondenceRightIntermediateAmbientInclusion]
  infer_instance

/-- Z-first support intersection has the exact ideal sum, not its radical. -/
theorem correspondenceRightIntermediateAmbientInclusion_ker [IsSeparated h] :
    (correspondenceRightIntermediateAmbientInclusion f g h i z w v).ker =
      (correspondenceSecondAmbientInclusion f g h i).ker ⊔
        (correspondenceTripleSupportProductInclusion f g h i z w v).ker :=
  Scheme.Hom.ker_comp_eq_sup_of_isPullback _ _ _ _
    (correspondenceRightIntermediate_ambient_isPullback f g h i z w v)

/-- The common triple point maps to the actual right first stage by native reassociation. -/
abbrev correspondenceTripleIncidenceToRightSupportProduct :
    correspondenceTripleIncidence f g h i z w v ⟶
      correspondenceRightIntermediateSupportProduct f g h i z w v :=
  (correspondenceTripleIncidenceAssoc f g h i z w v).hom ≫
    correspondenceRightTripleIncidenceToSupportProduct f g h i z w v

/-- Reassociation leaves the common full coefficient-support map unchanged. -/
@[reassoc]
theorem correspondenceTripleIncidenceToRightSupportProduct_support :
    correspondenceTripleIncidenceToRightSupportProduct f g h i z w v ≫
        correspondenceRightIntermediateToTripleSupport f g h i z w v =
      correspondenceTripleIncidenceToTripleSupport f g h i z w v := by
  apply (correspondenceTripleSupport_right_isPullback f g h i z w v).hom_ext
  · simp [correspondenceTripleIncidenceToRightSupportProduct,
      correspondenceRightTripleIncidenceToSupportProduct, pullback.mapDesc, pullback.map,
      correspondenceTripleSupportFirstProjection, correspondenceTripleIncidenceToTripleSupport,
      correspondenceTripleIncidenceFst, Category.assoc]
  · simp only [Category.assoc, correspondenceRightIntermediateToTripleSupport_rightPair]
    apply pullback.hom_ext <;>
      simp [correspondenceRightTripleIncidenceToSupportProduct, pullback.mapDesc, pullback.map,
        correspondenceTripleSupportRightProjection, correspondenceRightExteriorProjection,
        Category.assoc]

/-- The right first stage has the same original common sixfold image. -/
@[reassoc]
theorem correspondenceTripleIncidenceToRightSupportProduct_ambient :
    correspondenceTripleIncidenceToRightSupportProduct f g h i z w v ≫
        correspondenceRightIntermediateAmbientInclusion f g h i z w v =
      correspondenceTripleIncidenceSixfoldInclusion f g h i z w v := by
  rw [correspondenceRightIntermediateAmbientInclusion,
    correspondenceRightIntermediate_ambient_comm, ← Category.assoc,
    correspondenceTripleIncidenceToRightSupportProduct_support]
  exact (correspondenceTripleIncidence_sixfold_isPullback f g h i z w v).w.symm

end Stacks.Chow
