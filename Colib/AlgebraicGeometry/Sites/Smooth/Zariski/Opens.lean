/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Cohomology.GenericOpen
public import Colib.AlgebraicGeometry.Sites.Smooth.Zariski.Topology
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import StacksFrontier.AlgebraicGeometry.Topologies.Zariski.SmallSiteExtension
import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence
import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.BigSiteSheafCohomology

/-! # Restriction to the opens of a smooth Zariski object -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

private theorem preservesEqualizersOfIsThin {C D : Type*} [Category* C] [Category* D]
    [Quiver.IsThin C] (F : C ⥤ D) : PreservesLimitsOfShape WalkingParallelPair F := by
  constructor
  intro K
  let f := K.map WalkingParallelPairHom.left
  let g := K.map WalkingParallelPairHom.right
  have h : f = g := Subsingleton.elim _ _
  let h' : (𝟙 _) ≫ f = (𝟙 _) ≫ g := congrArg (𝟙 _ ≫ ·) h
  let : PreservesLimit (parallelPair f g) F := by
    refine preservesLimit_of_preserves_limit_cone (isLimitIdFork h) ?_
    refine (isLimitMapConeForkEquiv F h').symm ?_
    let q := isLimitIdFork (congrArg F.map h)
    exact IsLimit.ofIsoLimit q (Fork.ext (Iso.refl _) (by
      change (𝟙 _) ≫ F.map (𝟙 _) = 𝟙 _
      exact (Category.id_comp _).trans (F.map_id _)))
  exact preservesLimit_of_iso_diagram _ (diagramIsoParallelPair K).symm

variable {S : Scheme.{u}} [IsNoetherian S] (X : SmoothSite S)

instance : PreservesLimitsOfShape WalkingCospan (opensFunctor X) := by
  refine preservesLimitsOfShape_walkingCospan_of_forall_isPullback ?_
  intro U V W f g _
  refine ⟨U ⊓ V, homOfLE inf_le_left, homOfLE inf_le_right, ?_, ?_⟩
  · exact (isPullback_iff_isLimit_binaryFan_of_isThin).2
      ⟨BinaryFan.IsLimit.mk _ (fun a b ↦ homOfLE (le_inf a.le b.le))
        (fun _ _ ↦ Subsingleton.elim _ _) (fun _ _ ↦ Subsingleton.elim _ _)
        (fun _ _ _ _ _ ↦ Subsingleton.elim _ _)⟩
  · apply IsPullback.of_map_of_faithful (forgetScheme S)
    exact isPullback_opens_inf_le f.le g.le

instance : PreservesLimitsOfShape WalkingParallelPair (opensFunctor X) :=
  preservesEqualizersOfIsThin (opensFunctor X)

set_option backward.isDefEq.respectTransparency false in
instance opensFunctor_isContinuous :
    (opensFunctor X).IsContinuous (Opens.grothendieckTopology X.left) (zariskiTopology S) := by
  let J := (Opens.grothendieckTopology X.left).toPrecoverage
  have hJ : J.toGrothendieck = Opens.grothendieckTopology X.left := by
    refine le_antisymm (GrothendieckTopology.toGrothendieck_toPrecoverage_le _) fun U R hR ↦ ?_
    rw [← GrothendieckTopology.arrows_mem_toPrecoverage_iff] at hR
    simpa using Precoverage.generate_mem_toGrothendieck hR
  rw [← hJ, zariskiTopology]
  refine Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy (opensFunctor X) J _ ?_
  intro U R hR
  obtain ⟨I, V, f, rfl⟩ := R.exists_eq_ofArrows
  rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows]
  apply (ofArrows_mem_zariskiPrecoverage_iff _).2
  refine ⟨?_, fun i ↦ inferInstanceAs (IsOpenImmersion (X.left.homOfLE (f i).le))⟩
  change Sieve.generate (Presieve.ofArrows V f) ∈ Opens.grothendieckTopology X.left U at hR
  rw [Opens.mem_grothendieckTopology] at hR
  intro x
  obtain ⟨W, _, ⟨_, b, _, ⟨i⟩, _⟩, hx⟩ := hR x.1 x.2
  refine ⟨i, ⟨⟨x.1, b.le hx⟩, Subtype.ext ?_⟩⟩
  change ((X.left.homOfLE (f i).le) ⟨x.1, b.le hx⟩).val = x.1
  rw [Scheme.homOfLE_apply]

private instance zariskiPrecoverage_pullbacksPreservedBy_forget :
    (zariskiPrecoverage S).PullbacksPreservedBy (forget S) where
  preservesPairwisePullbacks_of_mem {Y _} hR :=
    (nisnevichPrecoverage S).preservesPairwisePullbacks_of_mem
      (zariskiPrecoverage_le_nisnevichPrecoverage S Y hR)

omit [IsNoetherian S] in
private lemma forget_isContinuous_zariski :
    (forget S).IsContinuous (zariskiTopology S) (Scheme.zariskiTopology.over S) := by
  rw [zariskiTopology, Scheme.zariskiTopology, over_toGrothendieck_eq_toGrothendieck_comap_forget]
  apply Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy
  rw [zariskiPrecoverage, forgetScheme, Precoverage.comap_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Any Zariski cover of a smooth open object is refined by opens of the same ambient scheme. -/
instance opensFunctor_isCocontinuous :
    (opensFunctor X).IsCocontinuous (Opens.grothendieckTopology X.left) (zariskiTopology S) where
  cover_lift {U R} hR := by
    let G := forget S
    let : G.IsContinuous (zariskiTopology S) (Scheme.zariskiTopology.over S) :=
      forget_isContinuous_zariski
    have he : opensFunctor X ⋙ G = SmallZariski.relativeOpens S (G.obj X) := by
      change opensFunctor X ⋙ G = X.left.restrictFunctor ⋙ Over.map X.hom
      refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
      intro W V f
      apply Over.OverMorphism.ext
      simp [opensFunctor, Scheme.restrictFunctor, G]
    let : (opensFunctor X ⋙ G).IsCocontinuous (Opens.grothendieckTopology X.left)
        (Scheme.zariskiTopology.over S) :=
      he.symm ▸ SmallZariski.relativeOpens_isCocontinuous S (G.obj X)
    have h := (opensFunctor X ⋙ G).cover_lift (Opens.grothendieckTopology X.left)
      (Scheme.zariskiTopology.over S)
      ((CoverPreserving.of_isContinuous G _ _).cover_preserve hR)
    rwa [Sieve.functorPullback_comp, Sieve.functorPullback_functorPushforward_eq G] at h

/-- Restriction of a sheaf on the smooth Zariski site to the ordinary Zariski
site of a given object. -/
abbrev restrictZariskiToOpens (A : Type*) [Category* A] :
    Sheaf (zariskiTopology S) A ⥤ Sheaf (Opens.grothendieckTopology X.left) A :=
  (opensFunctor X).sheafPushforwardContinuous A _ _

theorem preservesFiniteColimits_restrictZariskiToOpens :
    PreservesFiniteColimits (restrictZariskiToOpens X AddCommGrpCat.{u + 1}) :=
  Stacks.Cohomology.BiggerSite.preservesFiniteColimits_sheafPushforwardContinuous _ _
    (opensFunctor X) _

theorem preservesInjectives_restrictZariskiToOpens
    [HasSheafify (zariskiTopology S) AddCommGrpCat.{u + 1}] :
    (restrictZariskiToOpens X AddCommGrpCat.{u + 1}).PreservesInjectiveObjects := by
  let J := Opens.grothendieckTopology X.left
  let : EssentiallySmall.{u + 1} X.left.Opens :=
    EssentiallySmall.mk' (AsSmall.equiv.{u, u, u + 1} : X.left.Opens ≌ AsSmall.{u + 1} X.left.Opens)
  let : HasSheafify J AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1} J
  exact Stacks.Cohomology.BiggerSite.preservesInjectiveObjects_sheafPushforwardContinuous.{u + 1}
    J (zariskiTopology S) (opensFunctor X)

end AlgebraicGeometry.Scheme.SmoothSite
