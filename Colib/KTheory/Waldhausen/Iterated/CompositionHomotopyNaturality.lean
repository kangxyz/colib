/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.PrespectrumCompositionHomotopy


/-!
# Naturality of the original transformation-composition comparison

Strict exact precomposition and postcomposition preserve the actual simplicial triangle,
its realization, and the existing two-parameter composition comparison. At prespectrum degree
zero, the equality is proved on the original based loops with a separate loop coordinate.
The comparison time, transformation time, and original structure time remain independent.
No replacement triangle, homotopy, or prespectrum map is introduced.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology CategoryTheory.Functor MonoidalCategory Topology.LoopPrespectrum
open scoped Simplicial Topology unitInterval
open CategoryTheory.Waldhausen.SmallWaldhausenCategory SSet
universe u

namespace CategoryTheory.Waldhausen.IteratedS

variable {V W T : WideSubcategory preservesZero.{u}} {F G H : V ⟶ W}
  (η : F.hom.toFunctor ⟶ G.hom.toFunctor) (θ : G.hom.toFunctor ⟶ H.hom.toFunctor)
  (hη : ∀ A, W.obj.waldhausen.weq (η.app A)) (hθ : ∀ A, W.obj.waldhausen.weq (θ.app A))

/-- Postwhiskering preserves the actual entire original simplicial triangle. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/CompositionHomotopyNaturality.lean:35"
  "adaptation"
    "Original whole transformation contraction, independent times and coefficient naturality"]
lemma stageTransformationTriangle_postcomp (n : ℕ) (J : W ⟶ T) :
    stageTransformationTriangle n (F := F ≫ J) (G := G ≫ J) (H := H ≫ J)
      (whiskerRight η J.hom.toFunctor) (whiskerRight θ J.hom.toFunctor)
      (fun A ↦ J.hom.isExact.weak _ (hη A)) (fun A ↦ J.hom.isExact.weak _ (hθ A)) =
      stageTransformationTriangle n η θ hη hθ ≫ (stages n).map J := by
  ext m z : 4
  exact stageTriangleFunction_postcomp n η θ hη hθ J m z.1 z.2

/-- Prewhiskering preserves the actual entire original simplicial triangle. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/CompositionHomotopyNaturality.lean:44"
  "adaptation"
    "Original whole transformation contraction, independent times and coefficient naturality"]
lemma stageTransformationTriangle_precomp (n : ℕ) (J : T ⟶ V) :
    stageTransformationTriangle n (F := J ≫ F) (G := J ≫ G) (H := J ≫ H)
      (whiskerLeft J.hom.toFunctor η) (whiskerLeft J.hom.toFunctor θ)
      (fun A ↦ hη (J.hom.toFunctor.obj A)) (fun A ↦ hθ (J.hom.toFunctor.obj A)) =
      (stages n).map J ▷ Δ[2] ≫ stageTransformationTriangle n η θ hη hθ := by
  ext m z : 4
  exact stageTriangleFunction_precomp n η θ hη hθ J m z.1 z.2

/-- Postcomposition preserves every point of the original realized triangle. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/CompositionHomotopyNaturality.lean:53"
  "adaptation"
    "Original whole transformation contraction, independent times and coefficient naturality"]
lemma stageTriangleRealization_postcomp (n : ℕ) (J : W ⟶ T)
    (x : stageSpace n V) (z : |(Δ[2] : SSet.{u})|) :
    stageTriangleRealization (F := F ≫ J) (G := G ≫ J) (H := H ≫ J)
      (whiskerRight η J.hom.toFunctor) (whiskerRight θ J.hom.toFunctor)
      (fun A ↦ J.hom.isExact.weak _ (hη A)) (fun A ↦ J.hom.isExact.weak _ (hθ A)) n (x, z) =
      SSet.toTop.map ((stages n).map J) (stageTriangleRealization η θ hη hθ n (x, z)) := by
  change SSet.toTop.map (stageTransformationTriangle n
      (F := F ≫ J) (G := G ≫ J) (H := H ≫ J)
      (whiskerRight η J.hom.toFunctor) (whiskerRight θ J.hom.toFunctor)
      (fun A ↦ J.hom.isExact.weak _ (hη A)) (fun A ↦ J.hom.isExact.weak _ (hθ A)))
      ((realizationProductSimplexIso ((stages n).obj V) 2).inv (x, z)) =
    SSet.toTop.map ((stages n).map J)
      (SSet.toTop.map (stageTransformationTriangle n η θ hη hθ)
        ((realizationProductSimplexIso ((stages n).obj V) 2).inv (x, z)))
  rw [stageTransformationTriangle_postcomp, Functor.map_comp]
  rfl

/-- Precomposition preserves every point of the original realized triangle. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/CompositionHomotopyNaturality.lean:71"
  "adaptation"
    "Original whole transformation contraction, independent times and coefficient naturality"]
lemma stageTriangleRealization_precomp (n : ℕ) (J : T ⟶ V)
    (x : stageSpace n T) (z : |(Δ[2] : SSet.{u})|) :
    stageTriangleRealization (F := J ≫ F) (G := J ≫ G) (H := J ≫ H)
      (whiskerLeft J.hom.toFunctor η) (whiskerLeft J.hom.toFunctor θ)
      (fun A ↦ hη (J.hom.toFunctor.obj A)) (fun A ↦ hθ (J.hom.toFunctor.obj A)) n (x, z) =
      stageTriangleRealization η θ hη hθ n (SSet.toTop.map ((stages n).map J) x, z) := by
  let p := (realizationProductSimplexIso ((stages n).obj T) 2).inv (x, z)
  have hn := ConcreteCategory.congr_hom
    (realizationProductSimplexIso_inv_whisker ((stages n).map J) 2) (x, z)
  change SSet.toTop.map ((stages n).map J ▷ Δ[2]) p =
    (realizationProductSimplexIso ((stages n).obj V) 2).inv
      (SSet.toTop.map ((stages n).map J) x, z) at hn
  change SSet.toTop.map (stageTransformationTriangle n
      (F := J ≫ F) (G := J ≫ G) (H := J ≫ H)
      (whiskerLeft J.hom.toFunctor η) (whiskerLeft J.hom.toFunctor θ)
      (fun A ↦ hη (J.hom.toFunctor.obj A)) (fun A ↦ hθ (J.hom.toFunctor.obj A))) p =
    SSet.toTop.map (stageTransformationTriangle n η θ hη hθ)
      ((realizationProductSimplexIso ((stages n).obj V) 2).inv
        (SSet.toTop.map ((stages n).map J) x, z))
  rw [stageTransformationTriangle_precomp, Functor.map_comp]
  exact congrArg (SSet.toTop.map (stageTransformationTriangle n η θ hη hθ)) hn

/-- Both actual composition-comparison times commute with exact postcomposition. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/CompositionHomotopyNaturality.lean:94"
  "adaptation"
    "Original whole transformation contraction, independent times and coefficient naturality"]
lemma stageTransformationCompositionHomotopy_postcomp (n : ℕ) (J : W ⟶ T)
    (r s : unitInterval) (x : stageSpace n V) :
    stageTransformationCompositionHomotopy (F := F ≫ J) (G := G ≫ J) (H := H ≫ J)
      (whiskerRight η J.hom.toFunctor) (whiskerRight θ J.hom.toFunctor)
      (fun A ↦ J.hom.isExact.weak _ (hη A)) (fun A ↦ J.hom.isExact.weak _ (hθ A)) n (r, (s, x)) =
      SSet.toTop.map ((stages n).map J)
        (stageTransformationCompositionHomotopy η θ hη hθ n (r, (s, x))) :=
  stageTriangleRealization_postcomp η θ hη hθ n J x
    ((SimplexCategory.toTopHomeo ⦋2⦌).symm (TheoremB.compositionTriangleHomotopy (r, s)))

/-- Both actual composition-comparison times commute with exact precomposition. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/CompositionHomotopyNaturality.lean:105"
  "adaptation"
    "Original whole transformation contraction, independent times and coefficient naturality"]
lemma stageTransformationCompositionHomotopy_precomp (n : ℕ) (J : T ⟶ V)
    (r s : unitInterval) (x : stageSpace n T) :
    stageTransformationCompositionHomotopy (F := J ≫ F) (G := J ≫ G) (H := J ≫ H)
      (whiskerLeft J.hom.toFunctor η) (whiskerLeft J.hom.toFunctor θ)
      (fun A ↦ hη (J.hom.toFunctor.obj A)) (fun A ↦ hθ (J.hom.toFunctor.obj A)) n (r, (s, x)) =
      stageTransformationCompositionHomotopy η θ hη hθ n
        (r, (s, SSet.toTop.map ((stages n).map J) x)) :=
  stageTriangleRealization_precomp η θ hη hθ n J x
    ((SimplexCategory.toTopHomeo ⦋2⦌).symm (TheoremB.compositionTriangleHomotopy (r, s)))

/-- Exact postcomposition preserves the original whole relative comparison, level by level
and at every pair of its independent times. Degree zero uses the actual based-loop map. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/CompositionHomotopyNaturality.lean:117"
  "adaptation"
    "Original whole transformation contraction, independent times and coefficient naturality"]
lemma prespectrumTransformationCompositionHomotopy_postcomp_level (J : W ⟶ T)
    (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumTransformationCompositionHomotopy
      (F := F ≫ J) (G := G ≫ J) (H := H ≫ J)
      (whiskerRight η J.hom.toFunctor) (whiskerRight θ J.hom.toFunctor)
      (fun A ↦ J.hom.isExact.weak _ (hη A)) (fun A ↦ J.hom.isExact.weak _ (hθ A))).level n
        (r, (s, x)) =
      (prespectrumMap J).map n
        ((prespectrumTransformationCompositionHomotopy η θ hη hθ).level n (r, (s, x))) := by
  cases n with
  | zero =>
    change Path (stagePoint 0 V) (stagePoint 0 V) at x
    apply Path.ext
    funext q
    exact stageTransformationCompositionHomotopy_postcomp η θ hη hθ 0 J r s (x q)
  | succ n =>
    exact stageTransformationCompositionHomotopy_postcomp η θ hη hθ n J r s x

/-- Exact precomposition preserves the original whole relative comparison, level by level
and at every pair of its independent times. Degree zero uses the actual based-loop map. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/CompositionHomotopyNaturality.lean:137"
  "adaptation"
    "Original whole transformation contraction, independent times and coefficient naturality"]
lemma prespectrumTransformationCompositionHomotopy_precomp_level (J : T ⟶ V)
    (n : ℕ) (r s : unitInterval) (x : (prespectrum T).space n) :
    (prespectrumTransformationCompositionHomotopy
      (F := J ≫ F) (G := J ≫ G) (H := J ≫ H)
      (whiskerLeft J.hom.toFunctor η) (whiskerLeft J.hom.toFunctor θ)
      (fun A ↦ hη (J.hom.toFunctor.obj A)) (fun A ↦ hθ (J.hom.toFunctor.obj A))).level n
        (r, (s, x)) =
      (prespectrumTransformationCompositionHomotopy η θ hη hθ).level n
        (r, (s, (prespectrumMap J).map n x)) := by
  cases n with
  | zero =>
    change Path (stagePoint 0 T) (stagePoint 0 T) at x
    apply Path.ext
    funext q
    exact stageTransformationCompositionHomotopy_precomp η θ hη hθ 0 J r s (x q)
  | succ n =>
    exact stageTransformationCompositionHomotopy_precomp η θ hη hθ n J r s x

/-- Postcomposition retains the original structure coordinate independently of both times. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/CompositionHomotopyNaturality.lean:156"
  "adaptation"
    "Original whole transformation contraction, independent times and coefficient naturality"]
lemma prespectrumTransformationCompositionHomotopy_postcomp_structure (J : W ⟶ T)
    (n : ℕ) (r s t : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumTransformationCompositionHomotopy
      (F := F ≫ J) (G := G ≫ J) (H := H ≫ J)
      (whiskerRight η J.hom.toFunctor) (whiskerRight θ J.hom.toFunctor)
      (fun A ↦ J.hom.isExact.weak _ (hη A)) (fun A ↦ J.hom.isExact.weak _ (hθ A))).level (n + 1)
        (r, (s, (prespectrum V).structureMap n x t)) =
      (prespectrum T).structureMap n
        ((prespectrumMap J).map n
          ((prespectrumTransformationCompositionHomotopy η θ hη hθ).level n
            (r, (s, x)))) t := by
  rw [prespectrumTransformationCompositionHomotopy_postcomp_level η θ hη hθ J,
    (prespectrumTransformationCompositionHomotopy η θ hη hθ).comm]
  exact congrArg (fun p ↦ p t)
    ((prespectrumMap J).comm n
      ((prespectrumTransformationCompositionHomotopy η θ hη hθ).level n (r, (s, x))))

/-- Precomposition retains the original structure coordinate independently of both times. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/CompositionHomotopyNaturality.lean:174"
  "adaptation"
    "Original whole transformation contraction, independent times and coefficient naturality"]
lemma prespectrumTransformationCompositionHomotopy_precomp_structure (J : T ⟶ V)
    (n : ℕ) (r s t : unitInterval) (x : (prespectrum T).space n) :
    (prespectrumTransformationCompositionHomotopy
      (F := J ≫ F) (G := J ≫ G) (H := J ≫ H)
      (whiskerLeft J.hom.toFunctor η) (whiskerLeft J.hom.toFunctor θ)
      (fun A ↦ hη (J.hom.toFunctor.obj A)) (fun A ↦ hθ (J.hom.toFunctor.obj A))).level (n + 1)
        (r, (s, (prespectrum T).structureMap n x t)) =
      (prespectrum W).structureMap n
        ((prespectrumTransformationCompositionHomotopy η θ hη hθ).level n
          (r, (s, (prespectrumMap J).map n x))) t := by
  rw [(prespectrumTransformationCompositionHomotopy
    (F := J ≫ F) (G := J ≫ G) (H := J ≫ H)
    (whiskerLeft J.hom.toFunctor η) (whiskerLeft J.hom.toFunctor θ)
    (fun A ↦ hη (J.hom.toFunctor.obj A)) (fun A ↦ hθ (J.hom.toFunctor.obj A))).comm]
  rw [prespectrumTransformationCompositionHomotopy_precomp_level η θ hη hθ J]

end CategoryTheory.Waldhausen.IteratedS

