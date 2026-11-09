/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingImageExteriorSquare
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ProperPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCoherentImage.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductAssociativity
public import StacksFrontier.AlgebraicGeometry.Chow.DominantPrimeCycle
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.SpecializationLift

/-!
# Fixed original labels in the full exterior finite-image square

This specializes native Stacks 02RG on cycles to the actual last-pair-incidence/image exterior
square. The native cycle theorem's sheaf premises are discharged by finite direct-image
coherence and affine base change for these actual finite maps, without the general proper
coherence theorem or a caller-supplied comparison. A single original point is inserted into
its own dimension-graded subgroup of native
`AlgebraicCycle`; extracting one coefficient afterwards retains the original point label.
No Chow quotient or replacement cycle model is used.

The first support is integral, so the native field-dimension theorem gives its relative
dimension over an arbitrary field. Its ambient schemes may be disconnected or have different
component dimensions. The two exterior schemes and the scheme-theoretic intermediate image
remain unreduced. Native `flatPullbackWeight` retains the multiplicity of the full inverse
image of each integral component, including nonreduced inseparable products.

The fixed-label identity uses actual second projections and keeps both labels: an exterior point
  contributes only when its
original projection is the specified original point and its finite image is the specified
image-exterior point. It retains the image-side flat multiplicity as well as the source-side
one. It does not identify those two multiplicities with one, nor does it replace them by
arbitrary chosen weights. Translating these native multiplicities into the local-ring fibre
length formulas is a separate native coefficient comparison.

Providers: Stacks 02RG on cycles, `properPushforward_single`, `flatPullback_apply`,
`relativeDimension_eq_of_finite_residueField`, and
`relativeDimension_of_isIntegral_over_field` at the pinned Stacks owners.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

attribute [local instance] isIntegral_integralComponentAt

variable (K : Type u) [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)


/-- The fixed first integral support has a canonical relative dimension over the field. -/
abbrev correspondenceFirstSupportDimension : ℕ :=
  (relativeDimension ((fieldChowSituation K)).dimensionFunction ((((integralComponentAt
    z).subschemeι ≫ pullback.snd f g) ≫ g))
    (genericPoint (integralComponentAt z).subscheme)).toNat

/-- The image exterior projection has the first support's dimension, without an ambient
connectedness, equidimensionality, or perfect-field hypothesis. -/
theorem relativeDimension_correspondenceRightImageExteriorProjection
    [LocallyOfFiniteType (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g)] :
    AlgebraicGeometry.RelativeDimension
      (correspondenceRightImageExteriorProjection f g h i z w v)
      (correspondenceFirstSupportDimension K f g z) := by
  let sJ := ((correspondenceIncidenceMap g h i w v).imageι ≫ pullback.fst g i) ≫ g
  let sF := ((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g
  exact AlgebraicGeometry.RelativeDimension.of_isPullback
    (IsPullback.of_hasPullback sF sJ)
    (relativeDimension_of_isIntegral_over_field K sF)

open Classical in
/-- Native 02RG regroups one fixed original label through the actual finite exterior square.
All exterior points with that original label and the specified finite image remain in the sum. -/
@[stacks 02RG "coefficient specialization at one original label in the actual full exterior square"]
theorem correspondenceRightImage_fixedLabel_pushPull
    [IsSeparated i] [LocallyOfFiniteType (((correspondenceIncidenceMap g h i w v).imageι ≫
      pullback.fst g i) ≫ g)] [LocallyOfFiniteType ((((integralComponentAt z).subschemeι ≫
      pullback.snd f g) ≫ g))]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (t : (correspondenceIncidence g h i w v)) (p : (correspondenceRightIntermediateImageProduct f
      g h i z w v)) (hp : (correspondenceRightImageExteriorProjection f g h i z w v) p =
      ((correspondenceIncidenceMap g h i w v).toImage) t) :
    let C := fieldChowSituation K
    let q := (correspondenceIncidenceMap g h i w v).toImage
    let q' := correspondenceRightIntermediateImageMap f g h i z w v
    let π := correspondenceRightExteriorProjection f g h i z w v
    let π' := correspondenceRightImageExteriorProjection f g h i z w v
    let sJ := ((correspondenceIncidenceMap g h i w v).imageι ≫ pullback.fst g i) ≫ g
    let sI := q ≫ sJ
    let sE := π ≫ sI
    let sT := π' ≫ sJ
    letI := isFinite_correspondenceIncidenceToImage g h i w v hw hv
    letI := isFinite_correspondenceRightIntermediateImageMap f g h i z w v hw hv
    let d := relativeDimension (C).dimensionFunction sI t
    let r := correspondenceFirstSupportDimension K f g z
    ((q).residueDegree t : ℤ) * flatPullbackWeight C sT π' (d + (r : ℤ)) p =
      ∑ᶠ η ∈ (q').base ⁻¹' {p},
        if π η = t then
          flatPullbackWeight C sE π (d + (r : ℤ)) η * ((q').residueDegree η : ℤ)
        else 0 := by
  dsimp only
  let C := fieldChowSituation K
  let I := correspondenceIncidence g h i w v
  let J := correspondenceIntermediateImage g h i w v
  let E := correspondenceRightIntermediateSupportProduct f g h i z w v
  let T := correspondenceRightIntermediateImageProduct f g h i z w v
  let q := (correspondenceIncidenceMap g h i w v).toImage
  let q' := correspondenceRightIntermediateImageMap f g h i z w v
  let π := correspondenceRightExteriorProjection f g h i z w v
  let π' := correspondenceRightImageExteriorProjection f g h i z w v
  let sJ := ((correspondenceIncidenceMap g h i w v).imageι ≫ pullback.fst g i) ≫ g
  let sV := (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g)
  let sI := q ≫ sJ
  let sE := π ≫ sI
  let sT := π' ≫ sJ
  classical
  let := isFinite_correspondenceIncidenceToImage g h i w v hw hv
  let := isFinite_correspondenceRightIntermediateImageMap f g h i z w v hw hv
  let d := relativeDimension (C).dimensionFunction sI t
  let r := correspondenceFirstSupportDimension K f g z
  let α : CycleGroup C sI d :=
    ⟨Function.locallyFinsuppWithin.single t (1 : ℤ), by
      rw [mem_cyclesOfDimension_iff_forall_point]
      intro a ha
      have hat : a = t := by
        by_contra hat
        exact ha (by simp [Function.locallyFinsuppWithin.single_apply, hat])
      subst a
      rfl⟩
  have hq : relativeDimension (C).dimensionFunction sI t =
      relativeDimension (C).dimensionFunction sJ (q t) :=
    relativeDimension_eq_of_finite_residueField (C).dimensionFunction sJ q t
      (residueField_finite_of_locallyQuasiFinite q t)
  have hbase : q' ≫ sT = sE := by
    simpa only [Category.assoc] using
      congrArg (fun a : E ⟶ J => a ≫ sJ)
        (correspondenceRightIntermediateImageMap_projection f g h i z w v)
  have hq' (η : E) : relativeDimension (C).dimensionFunction sE η =
      relativeDimension (C).dimensionFunction sT (q' η) := by
    rw [← hbase]
    exact relativeDimension_eq_of_finite_residueField (C).dimensionFunction sT q' η
      (residueField_finite_of_locallyQuasiFinite q' η)
  have : IsLocallyNoetherian I := LocallyOfFiniteType.isLocallyNoetherian sI
  have : IsLocallyNoetherian J := LocallyOfFiniteType.isLocallyNoetherian sJ
  have : IsLocallyNoetherian E := LocallyOfFiniteType.isLocallyNoetherian sE
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  let F (a : I) : (I).Modules :=
    (Scheme.Modules.pushforward (integralComponentAt a).subschemeι).obj
      (Ample.unitModule (integralComponentAt a).subscheme)
  have hcoh (a : I) : (F a).IsCoherent :=
    ClosedImmersionCoherentImage.isCoherent_pushforward_unit (integralComponentAt a).subschemeι
  have hpush (a : I) : ((Scheme.Modules.pushforward q).obj (F a)).IsCoherent := by
    have := hcoh a
    exact Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite
      q (F a)
  have hpush' (a : I) :
      ((Scheme.Modules.pushforward q').obj ((Scheme.Modules.pullback π).obj (F a))).IsCoherent := by
    have := hcoh a
    have := AlgebraicGeometry.isCoherent_pullback π (F a)
    exact Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite
      q' ((Scheme.Modules.pullback π).obj (F a))
  have hbc (a : I) : IsIso
      ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans
        (correspondenceRightIntermediateImageMap_isPullback f g h i z w v).w).app (F a)) := by
    have : (F a).IsQuasicoherent :=
      ClosedImmersionCoherentImage.isQuasicoherent_pushforward_unit
        (integralComponentAt a).subschemeι
    exact Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom
      (correspondenceRightIntermediateImageMap_isPullback f g h i z w v) (F a)
  have H := flatPullback_properPushforward C sI sJ sE sT
    q π' π q' (correspondenceRightIntermediateImageMap_isPullback f g h i z w v)
    rfl rfl rfl r
    (relativeDimension_correspondenceRightImageExteriorProjection K f g h i z w v) d α
    hpush hpush' hbc
  have He := congrArg (fun a : CycleGroup C sT (d + (r : ℤ)) => a.1 p) H
  rw [flatPullback_apply] at He
  have hsingle := properPushforward_single C sI sJ q rfl d t α rfl
  rw [ite_eq_left hq.symm] at hsingle
  rw [hsingle, properPushforward_apply] at He
  have hp' : π' p = q t := hp
  simpa only [flatPullback_apply, hq', ite_true, α,
    Function.locallyFinsuppWithin.single_apply, hp', ite_mul, one_mul, zero_mul] using He

end Stacks.Chow
