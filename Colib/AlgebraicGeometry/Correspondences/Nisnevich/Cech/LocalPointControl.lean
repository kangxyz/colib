/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Nisnevich.Cech.LocalExactness

/-!
# Point provenance retained by the native local Cech contraction

The native contraction already constructs point lifts. This leaf retains them
through the actual source-graph incidence presentation and common-support map,
without changing the signed boundary, Tor coefficients or residue degrees.

Source: motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/AlgebraicGeometry/Correspondences/Nisnevich/Points/ControlledCechKernel.lean`,
blob `a91284832520c67b65eac75c556601e81c9f2937`.
The proof extends the existing native LocalExactness construction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow
open Function.locallyFinsuppWithin
open scoped BigOperators

universe u

namespace AlgebraicGeometry.Cor

variable (k : Type u) [Field k]
  {X Y U V : Scheme.SmoothSite (Spec (.of k))}

/-- Every surviving boundary point retains an original input support point and
an actual point of the whole common-support pullback. -/
theorem exists_cech_boundary_of_common_support_lift_with_point_lift
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
          β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackSnd q q) ∧
      ∀ v, β.val v ≠ 0 → ∀ z : (integralComponentAt v).subscheme,
        ∃ a : α.property.1.toFinset, ∃ w : (integralComponentAt a.val).subscheme,
        ∃ d : (pullback (j ≫ pullback.fst X.hom Y.hom) g.left : Scheme),
          ((integralComponentAt a.val).subschemeι ≫ pullback.fst X.hom V.hom) w =
            g.left (((integralComponentAt v).subschemeι ≫
              pullback.fst U.hom (Scheme.SmoothSite.etalePullback q q).hom) z) ∧
          ((integralComponentAt a.val).subschemeι ≫ pullback.snd X.hom V.hom) w =
            ((integralComponentAt v).subschemeι ≫
              pullback.snd U.hom (Scheme.SmoothSite.etalePullback q q).hom ≫
              (Scheme.SmoothSite.etalePullbackFst q q).left) z ∧
          pullback.snd (j ≫ pullback.fst X.hom Y.hom) g.left d =
            ((integralComponentAt v).subschemeι ≫
              pullback.fst U.hom (Scheme.SmoothSite.etalePullback q q).hom) z ∧
          b d = ((integralComponentAt v).subschemeι ≫
              pullback.snd U.hom (Scheme.SmoothSite.etalePullback q q).hom ≫
              (Scheme.SmoothSite.etalePullbackSnd q q).left) z := by
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
  obtain ⟨β, hβ, hpoints⟩ := exists_cech_boundary_of_incidence_presentation_with_point_lift
    k ((graphFunctor k).map g ≫ α) a (fun i : I => i.1.val) ha hadm
    (fun i : I => α.val i.1.val) q D t s j' hs₁ hs₂ htsource httarget hsum (by
      let Γg : Cor.mk U ⟶ Cor.mk X := (graphFunctor k).map g
      let Γq : Cor.mk V ⟶ Cor.mk Y := (graphFunctor k).map q
      change (Γg ≫ α) ≫ Γq = 0
      change α ≫ Γq = 0 at hzero
      rw [Category.assoc, hzero, comp_zero])
  refine ⟨β, hβ.symm, ?_⟩
  intro v hv z
  obtain ⟨i, w, hwsource, hwfirst, hwsecond⟩ := hpoints v hv z
  let m := (integralComponentAt (a i)).subschemeι ≫ pullback.snd U.hom X.hom
  let n := (integralComponentAt i.1.val).subschemeι ≫ pullback.fst X.hom V.hom
  have hsource : pullback.snd m n ≫ n =
      correspondenceIncidenceLeft U.hom X.hom V.hom (a i) i.1.val ≫ g.left := by
    rw [← pullback.condition]
    have he := congrArg (fun e => pullback.fst m n ≫ e)
      (integralComponentAt_graphMap_snd U.hom X.hom g.left
        (MorphismProperty.Over.w g) i.2.val)
    simpa only [m, a, correspondenceIncidenceLeft, Category.assoc] using he
  have hd : pullback.snd p g.left (t i w) =
      correspondenceIncidenceLeft U.hom X.hom V.hom (a i) i.1.val w := by
    exact congrArg (fun e => e w)
      (graphIncidenceToCommonSupport_snd X.hom V.hom Y.hom q.left
        (MorphismProperty.Over.w q) i.1.val j (r i.1.val (hsupport i))
        (hr i.1.val (hsupport i)) U.hom g.left (MorphismProperty.Over.w g) i.2)
  refine ⟨i.1, pullback.snd m n w, t i w, ?_, hwfirst, hd.trans hwsource, ?_⟩
  · exact (congrArg (fun e => e w) hsource).trans (congrArg g.left hwsource)
  · have hst : s ≫ pullback.snd U.hom V.hom = b := pullback.lift_snd _ _ _
    rw [Category.assoc, hst] at hwsecond
    exact hwsecond

end AlgebraicGeometry.Cor
