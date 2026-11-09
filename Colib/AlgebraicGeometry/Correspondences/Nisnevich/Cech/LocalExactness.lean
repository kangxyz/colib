/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.Correspondences.Graph.PrecompositionSum
public import Colib.AlgebraicGeometry.Correspondences.Nisnevich.Cech.Contraction
public import Colib.AlgebraicGeometry.Correspondences.Nisnevich.Cech.FiniteSupport
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.FiniteLifting
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.ResidueFieldMap

/-!
# Pointed local Čech exactness for actual signed finite correspondences

The actual finite support of a native correspondence has one common finite
closed image after postcomposition with the covering morphism. The whole image
is lifted over one pointed smooth Nisnevich neighborhood. The original graph
precomposition expands over the original support and the generic points of the
new source, with the original integer coefficients and incidence Tor cycles.
The concrete common-support contraction supplies the actual Čech boundary.

The common support and its pullback are not reduced. The field is arbitrary,
and the smooth objects may be empty or disconnected. The zero correspondence
is handled without choosing an artificial support point. No graph fullness,
cycle comparison, or local exactness hypothesis is supplied by the caller.

The final endpoint asserts a pointed neighborhood at each source point and the
signed boundary identity there. It does not assert an additional simultaneous
all-point refinement property. The lower incidence contraction separately
retains its actual support-point lifts.

Implementation provenance: motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/AlgebraicGeometry/Correspondences/Nisnevich/Cech/LocalExactness.lean`.
The source's custom generators and integral cycles are replaced by the existing
native finite-correspondence subgroup, support points, and `AlgebraicCycle`.

Native leaf acceptance is recorded separately; no independent review is claimed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow
open Function.locallyFinsuppWithin
open scoped BigOperators

universe u

namespace AlgebraicGeometry.Cor

variable (k : Type u) [Field k]
  {X Y U V : Scheme.SmoothSite (Spec (.of k))}

/-- A lift of the whole common finite image contracts a signed relation after
an arbitrary source morphism. The original incidence presentation is derived,
and the concrete contraction proves all three graph/cycle identities. -/
@[colib_ref "motivic_source_a6805c4"
  "Correspondences/Nisnevich/Cech/LocalExactness.lean: \
exists_cech_boundary_of_common_support_lift"
  "adaptation" "actual finite support, original signed incidence presentation, and one \
whole nonreduced common-support lift"]
theorem exists_cech_boundary_of_common_support_lift
    (α : Cor.mk X ⟶ Cor.mk V) (q : V ⟶ Y) [Etale q.left]
    (hzero : α ≫ (graphFunctor k).map q = 0)
    (C : Scheme.{u}) (j : C ⟶ pullback X.hom Y.hom) [IsClosedImmersion j]
    [IsFinite (j ≫ pullback.fst X.hom Y.hom)]
    (r : ∀ a ∈ α.val.support, (integralComponentAt a).subscheme ⟶ C)
    (hr : ∀ a ha, r a ha ≫ j =
      correspondenceGraphPostcompositionMap X.hom V.hom Y.hom q.left
        (MorphismProperty.Over.w q) a)
    (g : U ⟶ X)
    (b : pullback (C := Scheme) (j ≫ pullback.fst X.hom Y.hom) g.left ⟶ V.left)
    (hb : b ≫ q.left = pullback.fst (j ≫ pullback.fst X.hom Y.hom) g.left ≫
      j ≫ pullback.snd X.hom Y.hom) :
    ∃ β : Cor.mk U ⟶ Cor.mk (Scheme.SmoothSite.etalePullback q q),
      (graphFunctor k).map g ≫ α =
        β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackFst q q) -
          β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackSnd q q) := by
  classical
  let p := j ≫ pullback.fst X.hom Y.hom
  let D := pullback p g.left
  let j' : D ⟶ pullback U.hom Y.hom := ClosedImageBaseChange.inclusion
    X.hom Y.hom U.hom g.left (MorphismProperty.Over.w g) j
  let s : D ⟶ pullback U.hom V.hom :=
    pullback.lift (j' ≫ pullback.fst U.hom Y.hom) b (by
      calc
        _ = (j' ≫ pullback.snd U.hom Y.hom) ≫ Y.hom := by
          simp only [Category.assoc, pullback.condition]
        _ = b ≫ V.hom := by
          dsimp only [j']
          rw [ClosedImageBaseChange.inclusion_snd, ← hb, Category.assoc,
            MorphismProperty.Over.w q])
  have hs₁ : s ≫ pullback.fst U.hom V.hom = j' ≫ pullback.fst U.hom Y.hom :=
    pullback.lift_fst _ _ _
  have hs₂ : s ≫ pullback.snd U.hom V.hom ≫ q.left =
      j' ≫ pullback.snd U.hom Y.hom := by
    rw [← Category.assoc, show s ≫ pullback.snd U.hom V.hom = b from
      pullback.lift_snd _ _ _, hb]
    exact (ClosedImageBaseChange.inclusion_snd X.hom Y.hom U.hom g.left
      (MorphismProperty.Over.w g) j).symm
  have : IsFinite (s ≫ pullback.fst U.hom V.hom) := by
    rw [hs₁]
    dsimp only [j']
    infer_instance
  have : IsFinite s := IsFinite.of_comp s (pullback.fst U.hom V.hom)
  let := (finite_genericPoints k (Cor.mk U)).fintype
  let I : Type u := ↥α.property.1.toFinset × genericPoints U.left
  have hsupport (i : I) : i.1.val ∈ α.val.support :=
    α.property.1.mem_toFinset.mp i.1.property
  let a (i : I) : pullback (C := Scheme) U.hom X.hom :=
    correspondenceGraphMap U.hom X.hom g.left (MorphismProperty.Over.w g) i.2.val
  have ha (i : I) : IsFiniteCorrespondencePoint U.hom X.hom (a i) :=
    isFiniteCorrespondencePoint_graphMap U.hom X.hom g.left
      (MorphismProperty.Over.w g) i.2
  have hadm (i : I) : IsFiniteCorrespondencePoint X.hom V.hom i.1.val :=
    α.property.2 i.1.val (hsupport i)
  let t (i : I) : correspondenceIncidence U.hom X.hom V.hom (a i) i.1.val ⟶ D :=
    graphIncidenceToCommonSupport X.hom V.hom Y.hom q.left
      (MorphismProperty.Over.w q) i.1.val j (r i.1.val (hsupport i))
      (hr i.1.val (hsupport i)) U.hom g.left (MorphismProperty.Over.w g) i.2
  have htfinite (i : I) : IsFinite (t i) :=
    isFinite_graphIncidenceToCommonSupport X.hom V.hom Y.hom q.left
      (MorphismProperty.Over.w q) i.1.val j (r i.1.val (hsupport i))
      (hr i.1.val (hsupport i)) U.hom g.left (MorphismProperty.Over.w g) i.2 (hadm i)
  let : ∀ i : I, IsFinite (t i) := htfinite
  have htsource (i : I) : t i ≫ s ≫ pullback.fst U.hom V.hom =
      correspondenceIncidenceLeft U.hom X.hom V.hom (a i) i.1.val := by
    rw [hs₁]
    dsimp only [j']
    rw [ClosedImageBaseChange.inclusion_fst]
    exact graphIncidenceToCommonSupport_snd X.hom V.hom Y.hom q.left
      (MorphismProperty.Over.w q) i.1.val j (r i.1.val (hsupport i))
      (hr i.1.val (hsupport i)) U.hom g.left (MorphismProperty.Over.w g) i.2
  have httarget (i : I) : t i ≫ j' ≫ pullback.snd U.hom Y.hom =
      correspondenceIncidenceRight U.hom X.hom V.hom (a i) i.1.val ≫ q.left := by
    dsimp only [j']
    rw [ClosedImageBaseChange.inclusion_snd]
    exact graphIncidenceToCommonSupport_target X.hom V.hom Y.hom q.left
      (MorphismProperty.Over.w q) i.1.val j (r i.1.val (hsupport i))
      (hr i.1.val (hsupport i)) U.hom g.left (MorphismProperty.Over.w g) i.2
  have hsum : ∑ i : I, α.val i.1.val •
      incidenceTorCorrespondence U.hom X.hom V.hom (a i) i.1.val (ha i) (hadm i) =
        (graphFunctor k).map g ≫ α := by
    exact (graph_comp_eq_sum_incidence k α g).symm
  obtain ⟨β, hβ, _⟩ := exists_cech_boundary_of_incidence_presentation_with_point_lift
    k ((graphFunctor k).map g ≫ α) a (fun i : I => i.1.val) ha hadm
    (fun i : I => α.val i.1.val) q D t s j' hs₁ hs₂ htsource httarget hsum (by
      let Γg : Cor.mk U ⟶ Cor.mk X := (graphFunctor k).map g
      let Γq : Cor.mk V ⟶ Cor.mk Y := (graphFunctor k).map q
      change (Γg ≫ α) ≫ Γq = 0
      change α ≫ Γq = 0 at hzero
      rw [Category.assoc, hzero, comp_zero])
  exact ⟨β, hβ.symm⟩

/-- Every signed relation for one completely decomposed étale arrow is an
actual Čech boundary after a pointed smooth Nisnevich neighborhood. The Tor
composition, signed coefficients, and finite-image residue degrees are unchanged. -/
@[colib_ref "motivic_source_a6805c4"
  "Correspondences/Nisnevich/Cech/LocalExactness.lean: exists_nisnevich_cech_boundary"
  "adaptation" "native signed correspondence relations and one pointed whole-support \
Nisnevich lift over an arbitrary field",
  colib_tag "COL-0370",
  colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Nisnevich/Cech/LocalExactness.lean"
  "adaptation" "Signed Nisnevich Cech local exactness"]
theorem exists_nisnevich_cech_boundary
    (α : Cor.mk X ⟶ Cor.mk V) (q : V ⟶ Y) [Etale q.left]
    (hq : ∀ y : Y.left, ∃ v : V.left,
      q.left v = y ∧ IsIso (q.left.residueFieldMap v))
    (hzero : α ≫ (graphFunctor k).map q = 0) (x : X.left) :
    ∃ (U : Scheme.SmoothSite (Spec (.of k))) (g : U ⟶ X), Etale g.left ∧
      ∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u) ∧
      ∃ β : Cor.mk U ⟶ Cor.mk (Scheme.SmoothSite.etalePullback q q),
        (graphFunctor k).map g ≫ α =
          β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackFst q q) -
            β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackSnd q q) := by
  classical
  by_cases hα : α = 0
  · subst α
    refine ⟨X, 𝟙 X, ?_, x, rfl, ?_, 0, ?_⟩
    · change Etale (𝟙 X.left)
      infer_instance
    · change IsIso ((𝟙 X.left : X.left ⟶ X.left).residueFieldMap x)
      infer_instance
    · let Γid : Cor.mk X ⟶ Cor.mk X := (graphFunctor k).map (𝟙 X)
      let Γ₁ : Cor.mk (Scheme.SmoothSite.etalePullback q q) ⟶ Cor.mk V :=
        (graphFunctor k).map (Scheme.SmoothSite.etalePullbackFst q q)
      let Γ₂ : Cor.mk (Scheme.SmoothSite.etalePullback q q) ⟶ Cor.mk V :=
        (graphFunctor k).map (Scheme.SmoothSite.etalePullbackSnd q q)
      change Γid ≫ (0 : Cor.mk X ⟶ Cor.mk V) =
        (0 : Cor.mk X ⟶ Cor.mk (Scheme.SmoothSite.etalePullback q q)) ≫ Γ₁ -
          (0 : Cor.mk X ⟶ Cor.mk (Scheme.SmoothSite.etalePullback q q)) ≫ Γ₂
      simp
  have hne : α.val.support.Nonempty := by
    by_contra h
    apply hα
    apply Subtype.ext
    ext a
    change α.val a = 0
    by_contra ha
    exact h ⟨a, by simpa only [support, Function.mem_support] using ha⟩
  obtain ⟨C, j, hj, hp, hfac⟩ := exists_common_finite_image_of_correspondence
    X.hom V.hom Y.hom q.left (MorphismProperty.Over.w q) α hne
  let : IsClosedImmersion j := hj
  let : IsFinite (j ≫ pullback.fst X.hom Y.hom) := hp
  choose r hr using hfac
  let p : C ⟶ X.left := j ≫ pullback.fst X.hom Y.hom
  let target : C ⟶ Y.left := j ≫ pullback.snd X.hom Y.hom
  let l : pullback target q.left ⟶ C := pullback.fst target q.left
  have : Etale l := by dsimp only [l]; infer_instance
  have : IsSeparated l := by dsimp only [l]; infer_instance
  have hl : ∀ z : C, p z = x → ∃ v : (pullback target q.left : Scheme),
      l v = z ∧ IsIso (l.residueFieldMap v) := by
    intro z _
    obtain ⟨v, hv, hres⟩ := hq (target z)
    obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := target) (g := q.left) z v hv.symm
    refine ⟨w, hw₁, ?_⟩
    exact isIso_residueFieldMap_pullback_fst_of_right target q.left w (by
      rw [hw₂]
      exact hres)
  obtain ⟨U, g, hg, u, hu, hgu, b₀, hb₀⟩ :=
    Scheme.SmoothSite.exists_nisnevich_lift_of_isFinite X p x l hl
  let b : pullback p g.left ⟶ V.left := b₀ ≫ pullback.snd target q.left
  have hb : b ≫ q.left = pullback.fst p g.left ≫ target := by
    dsimp only [b]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hb₀]
  obtain ⟨β, hβ⟩ := exists_cech_boundary_of_common_support_lift
    k α q hzero C j r hr g b hb
  exact ⟨U, g, hg, u, hu, hgu, β, hβ⟩

end AlgebraicGeometry.Cor
