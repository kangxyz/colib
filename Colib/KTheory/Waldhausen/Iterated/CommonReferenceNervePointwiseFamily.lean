/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNerveCompactFamily
public import Colib.KTheory.Waldhausen.Iterated.SimplexPostwhiskering

/-!
# Pointwise evaluation and postcomposition in the actual reference nerve

Evaluation at a nerve point uses a constant compact parameter. The full specified
attaching map acts by the original postcomposition at each native level, including
level zero, because it carries every characteristic simplex to the corresponding
reanchored simplex. This provides no continuity on an arbitrary nerve product.

Adapted from `CommonReferenceNervePointwiseFamily.lean`,
`CommonReferenceNerveWhiskering.lean` and `CommonReferenceNerveCompactAttachment.lean`
in Quillen K-theory at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor Convexity
open scoped Simplicial Topology unitInterval
universe u v

namespace CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve
open SmallWaldhausenCategory

variable {V W T : WideSubcategory preservesZero.{u}} {F : V ⟶ W}

variable {U : WideSubcategory preservesZero.{u}} {G : U ⟶ T} in
/-- Every entire original simplex parameter follows the same full-node function. -/
theorem mapParameter_parameter (f : Node F → Node G) {k : ℕ}
    (N : Fin (k + 1) → Node F) (z : StdSimplex ℝ (Fin (k + 1))) :
    mapParameter f (parameter F N z) = parameter G (fun i ↦ f (N i)) z := by
  have he : SSet.yonedaEquiv.symm (Codiscrete.functor N) ≫
      nerveMap (Codiscrete.functorOfFun f) =
        SSet.yonedaEquiv.symm (Codiscrete.functor (fun i ↦ f (N i))) := by
    apply SSet.yonedaEquiv.injective
    simp only [SSet.yonedaEquiv_comp, SSet.yonedaEquiv.apply_symm_apply]
    rfl
  change (SSet.toTop.map (SSet.yonedaEquiv.symm (Codiscrete.functor N)) ≫
    SSet.toTop.map (nerveMap (Codiscrete.functorOfFun f)))
      ((SimplexCategory.toTopHomeo ⦋k⦌).symm z) = _
  rw [← Functor.map_comp, he]
  rfl

/-- The original attached finite simplex evaluates by the actual postcomposition. -/
theorem simplexFamily_attachPostcomp (F : V ⟶ W) (J : W ⟶ T) (G : V ⟶ T)
    (ε : G.hom.toFunctor ≅ (F ≫ J).hom.toFunctor) {k : ℕ}
    (N : Fin (k + 1) → Node F) (n : ℕ) (z : StdSimplex ℝ (Fin (k + 1)))
    (x : (prespectrum V).space n) :
    prespectrumSimplexFamily (ModelSimplex.ofIsos G
        (fun i ↦ (attachPostcompNode F J G ε (N i)).1)
        (fun i ↦ (attachPostcompNode F J G ε (N i)).2)) n (z, x) =
      (prespectrumMap J).map n (prespectrumSimplexFamily
        (ModelSimplex.ofIsos F (fun i ↦ (N i).1) (fun i ↦ (N i).2)) n (z, x)) := by
  change prespectrumSimplexFamily
    (ModelSimplex.reanchorSimplex ε (fun i ↦
      ⟨(N i).1 ≫ J, isoWhiskerRight (N i).2 J.hom.toFunctor⟩)) n (z, x) = _
  rw [ModelSimplex.reanchorSimplex_eq, ← ModelSimplex.ofIsos_postcomp]
  exact prespectrumSimplexFamily_postcomp _ J n z x

variable (F)

/-- Evaluate a nerve point using the existing family with constant compact parameter `Unit`. -/
def pointwisePrespectrumFamily (n : ℕ) (y : |nerve (Codiscrete (Node F))|)
    (x : (prespectrum V).space n) : (prespectrum W).space n :=
  compactPrespectrumFamily F (ContinuousMap.const Unit y) n ((), x)

/-- Every full-node simplex representative gives the same original native value. -/
theorem pointwisePrespectrumFamily_parameter {k : ℕ} (N : Fin (k + 1) → Node F)
    (n : ℕ) (z : StdSimplex ℝ (Fin (k + 1))) (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily F n (parameter F N z) x =
      prespectrumSimplexFamily
        (ModelSimplex.ofIsos F (fun i ↦ (N i).1) (fun i ↦ (N i).2)) n (z, x) :=
  compactPrespectrumFamily_eq_simplex F (ContinuousMap.const Unit (parameter F N z))
    N () z rfl n x

/-- Pointwise evaluation agrees with every original compact-parameter family. -/
theorem pointwisePrespectrumFamily_eq_compact
    {S : Type v} [TopologicalSpace S] [CompactSpace S]
    (p : C(S, |nerve (Codiscrete (Node F))|)) (n : ℕ) (t : S)
    (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily F n (p t) x = compactPrespectrumFamily F p n (t, x) := by
  obtain ⟨k, N, z, hz⟩ := exists_parameter F (p t)
  calc
    _ = prespectrumSimplexFamily
        (ModelSimplex.ofIsos F (fun i ↦ (N i).1) (fun i ↦ (N i).2)) n (z, x) := by
      rw [← hz]
      exact pointwisePrespectrumFamily_parameter F N n z x
    _ = _ := (compactPrespectrumFamily_eq_simplex F p N t z hz.symm n x).symm

/-- Restriction to any compact parameter has the existing joint continuity proof. -/
theorem pointwisePrespectrumFamily_compact_continuous
    {S : Type v} [TopologicalSpace S] [CompactSpace S]
    (p : C(S, |nerve (Codiscrete (Node F))|)) (n : ℕ) :
    Continuous (fun z : S × (prespectrum V).space n ↦
      pointwisePrespectrumFamily F n (p z.1) z.2) := by
  have h : (fun z : S × (prespectrum V).space n ↦
      pointwisePrespectrumFamily F n (p z.1) z.2) = compactPrespectrumFamily F p n := by
    funext z
    exact pointwisePrespectrumFamily_eq_compact F p n z.1 z.2
  rw [h]
  exact (compactPrespectrumFamily F p n).continuous

/-- The exact original point is preserved at every level, including zero. -/
theorem pointwisePrespectrumFamily_point (n : ℕ) (y : |nerve (Codiscrete (Node F))|) :
    pointwisePrespectrumFamily F n y ((prespectrum V).point n) =
      (prespectrum W).point n :=
  compactPrespectrumFamily_point F (ContinuousMap.const Unit y) n ()

/-- The structure coordinate is independent of the fixed nerve parameter. -/
theorem pointwisePrespectrumFamily_structure (n : ℕ)
    (y : |nerve (Codiscrete (Node F))|) (x : (prespectrum V).space n) (t : I) :
    pointwisePrespectrumFamily F (n + 1) y ((prespectrum V).structureMap n x t) =
      (prespectrum W).structureMap n (pointwisePrespectrumFamily F n y x) t :=
  compactPrespectrumFamily_structure F (ContinuousMap.const Unit y) n () x t

/-- Level zero acts on the actual original input loop at its independent loop time. -/
theorem pointwisePrespectrumFamily_zero_apply (y : |nerve (Codiscrete (Node F))|)
    (γ : Path (stagePoint 0 V) (stagePoint 0 V)) (ℓ : I) :
    (show Path (stagePoint 0 W) (stagePoint 0 W) from
      pointwisePrespectrumFamily F 0 y γ) ℓ =
      compactStageFamily F 0 (ContinuousMap.const Unit y) ((), γ ℓ) := rfl

variable (J : W ⟶ T) (G : V ⟶ T)
  (ε : G.hom.toFunctor ≅ (F ≫ J).hom.toFunctor)

/-- The full-reference attachment evaluates correctly at every point of the actual nerve. -/
theorem pointwisePrespectrumFamily_attachPostcomp (n : ℕ)
    (y : |nerve (Codiscrete (Node F))|) (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily G n (mapParameter (attachPostcompNode F J G ε) y) x =
      (prespectrumMap J).map n (pointwisePrespectrumFamily F n y x) := by
  obtain ⟨k, N, z, hz⟩ := exists_parameter F y
  rw [← hz, mapParameter_parameter, pointwisePrespectrumFamily_parameter,
    pointwisePrespectrumFamily_parameter]
  exact simplexFamily_attachPostcomp F J G ε N n z x

end CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve
