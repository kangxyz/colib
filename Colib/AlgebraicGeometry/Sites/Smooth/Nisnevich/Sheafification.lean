/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Topology
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.DenseSubsite.OneHypercoverDense
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Same-universe sheafification on the smooth Nisnevich site

For a quasi-separated base, affine open covers of a smooth separated
finite-type scheme remain in the smooth site. The affine objects form
an essentially small dense subsite. The pairwise intersections admit
affine covers by the same construction, so the ordinary sheaf
comparison can use limits in the universe of the scheme. The level-one
covering argument specializes Mathlib's `Functor.IsOneHypercoverDense.of_hasPullbacks`
to the pullbacks of the selected open immersions.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MorphismProperty

universe u u'

namespace AlgebraicGeometry.Scheme.SmoothSite

private abbrev affineObjects (S : Scheme.{u}) :=
  smoothSeparatedFiniteType.CostructuredArrow ⊤ Scheme.Spec S

private abbrev affineSpec (S : Scheme.{u}) : affineObjects S ⥤ SmoothSite S :=
  MorphismProperty.CostructuredArrow.toOver _ _ _

private abbrev affineTopology (S : Scheme.{u}) : GrothendieckTopology (affineObjects S) :=
  (affineSpec S).inducedTopology (nisnevichTopology S)

variable {S : Scheme.{u}} [QuasiSeparatedSpace S]

private def affineCoverObject (X : SmoothSite S) (i : X.left.affineOpenCover.I₀) :
    affineObjects S :=
  let f := X.left.affineOpenCover.f i ≫ X.hom
  .mk ⊤ f ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

private def affineCoverMap (X : SmoothSite S) (i : X.left.affineOpenCover.I₀) :
    (affineSpec S).obj (affineCoverObject X i) ⟶ X :=
  homMk (X.left.affineOpenCover.f i) rfl

private theorem affineCover_mem (X : SmoothSite S) :
    Sieve.ofArrows _ (affineCoverMap X) ∈ nisnevichTopology S X := by
  refine mem_nisnevichTopology_iff.mpr ⟨Presieve.ofArrows _ (affineCoverMap X), ?_, ?_⟩
  · rw [mem_nisnevichPrecoverage_iff, Presieve.map_ofArrows]
    exact Nisnevich.zariskiPrecoverage_le_precoverage _ X.left.affineOpenCover.openCover.mem₀
  · exact Sieve.le_generate _

private instance affineSpec_isCoverDense : (affineSpec S).IsCoverDense (nisnevichTopology S) where
  is_cover X := by
    refine (nisnevichTopology S).superset_covering ?_ (affineCover_mem X)
    intro Y f hf
    obtain ⟨i, g, rfl⟩ := Sieve.ofArrows.exists hf
    exact ⟨⟨affineCoverObject X i, g, affineCoverMap X i, rfl⟩⟩

private instance affineObjects_essentiallySmall : EssentiallySmall.{u} (affineObjects S) :=
  essentiallySmall_costructuredArrow_Spec _ fun _ _ _ h ↦
    let : Smooth _ := h.1.1
    inferInstance

private theorem affineSpec_isOneHypercoverDense :
    Functor.IsOneHypercoverDense.{u} (affineSpec S) (affineTopology S) (nisnevichTopology S) where
  nonempty_oneHypercoverDenseData X := by
    let (i : X.left.affineOpenCover.I₀) : Etale (affineCoverMap X i).left := by
      change Etale (X.left.affineOpenCover.f i)
      infer_instance
    let F := affineSpec S
    let P (i j : X.left.affineOpenCover.I₀) := pullback (affineCoverMap X i) (affineCoverMap X j)
    refine ⟨{
      I₀ := X.left.affineOpenCover.I₀
      X := affineCoverObject X
      f := affineCoverMap X
      I₁ i j := (P i j).left.affineOpenCover.I₀
      Y i j := affineCoverObject (P i j)
      p₁ i j k := F.preimage (affineCoverMap (P i j) k ≫ pullback.fst _ _)
      p₂ i j k := F.preimage (affineCoverMap (P i j) k ≫ pullback.snd _ _)
      w i j k := by
        change F.map (F.preimage _) ≫ _ = F.map (F.preimage _) ≫ _
        simp only [Functor.map_preimage, Category.assoc, pullback.condition]
      mem₀ := affineCover_mem X
      mem₁₀ i j W₀ p₁ p₂ hp := ?_ }⟩
    rw [← Functor.functorPushforward_mem_iff (affineTopology S) (nisnevichTopology S) F]
    refine (nisnevichTopology S).superset_covering ?_
      (Functor.IsCoverDense.functorPullback_pushforward_covering
        ⟨_, (nisnevichTopology S).pullback_stable
          (pullback.lift _ _ hp) (affineCover_mem (P i j))⟩)
    rintro T _ ⟨Z, q, r, ⟨_, s, _, ⟨k⟩, fac⟩, rfl⟩
    have fac₁ := fac =≫ pullback.fst (affineCoverMap X i) (affineCoverMap X j)
    have fac₂ := fac =≫ pullback.snd (affineCoverMap X i) (affineCoverMap X j)
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd] at fac₁ fac₂
    refine ⟨Z, q, r, ⟨k, F.preimage s, ?_, ?_⟩, rfl⟩
    · apply F.map_injective
      simpa only [Functor.map_comp, Functor.map_preimage] using fac₁.symm
    · apply F.map_injective
      simpa only [Functor.map_comp, Functor.map_preimage] using fac₂.symm

/-- The smooth Nisnevich site admits left exact sheafification in the scheme universe.
This uses the ordinary affine dense-subsite comparison. -/
theorem hasSheafify_nisnevichTopology (S : Scheme.{u}) [QuasiSeparatedSpace S]
    (A : Type u') [Category.{u} A] {FA : A → A → Type*} {CD : A → Type u}
    [∀ X Y, FunLike (FA X Y) (CD X) (CD Y)] [ConcreteCategory.{u} A FA]
    [HasLimits A] [HasColimits A] [PreservesLimits (CategoryTheory.forget A)]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)] :
    HasSheafify (nisnevichTopology S) A := by
  let F := affineSpec S
  let J := affineTopology S
  let : Functor.IsOneHypercoverDense.{u} F J (nisnevichTopology S) :=
    affineSpec_isOneHypercoverDense
  let : HasSheafify J A := hasSheafifyEssentiallySmallSite.{u} _ _
  let : (F.sheafPushforwardContinuous A J (nisnevichTopology S)).IsEquivalence :=
    Functor.isEquivalence_of_isOneHypercoverDense _ _ _ _
  exact Functor.IsDenseSubsite.hasSheafify_of_isEquivalence J (nisnevichTopology S) F

instance (S : Scheme.{u}) [QuasiSeparatedSpace S] :
    HasSheafify (nisnevichTopology S) (Type u) :=
  hasSheafify_nisnevichTopology S (Type u)

instance (S : Scheme.{u}) [QuasiSeparatedSpace S] :
    HasSheafify (nisnevichTopology S) AddCommGrpCat.{u} :=
  hasSheafify_nisnevichTopology S AddCommGrpCat.{u}

end AlgebraicGeometry.Scheme.SmoothSite

attribute [colib_tag "COL-0390"]
  AlgebraicGeometry.Scheme.SmoothSite.hasSheafify_nisnevichTopology
