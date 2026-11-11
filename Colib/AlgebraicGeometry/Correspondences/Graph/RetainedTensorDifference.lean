/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.RetainedPencilDifference
public import Colib.AlgebraicGeometry.Correspondences.Graph.RetainedGraphSpan
public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.GraphPole
public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.TensorSignedDifference

/-!
# Exact signed endpoints of the actual retained tensor pencil

The start is literally `(canonicalGraph tensor b) tensor d`, the end is
literally `a tensor n`, and the subtracted pole is the actual constant family of
`b tensor d`. The section a belongs to the graph line tensored with the line of b;
no identification of those two line modules is made. Full finite-flat support
cycles, regularity and all original signs are preserved.

The one endpoint is stated as the actual retained factor spans. Identifying
those with the original alpha/lambda and beta/psi graph compositions is the
separate flat graph-left whole-span comparison, not a premise of this theorem.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Divisors

universe u

namespace AlgebraicGeometry.Cor

open Scheme Scheme.PolynomialSectionPencil Scheme.RelativeCurvePencil
open Scheme.SmoothSite.Contraction

variable {k : Type u} [Field k] {S X V : Scheme.{u}}
  (t : S ⟶ Spec (.of k)) [IsSeparated t] (q : X ⟶ S) (r : V ⟶ S)
  [Smooth (q ≫ t)] [IsSeparated (q ≫ t)] [QuasiCompact (q ≫ t)]
  [Smooth (r ≫ t)] [IsSeparated (r ≫ t)] [QuasiCompact (r ≫ t)]
  [IsSeparated r] [SmoothOfRelativeDimension 1 r]
  (φ : X ⟶ V) (hφ : φ ≫ r = q)
  (T N : (pullback q r).Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback q r).sheaf.obj
    (pullback q r).ringCatSheaf.property T]
  [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback q r).sheaf.obj
    (pullback q r).ringCatSheaf.property N]

local notation "U" => SmoothSite.mk (q ≫ t)
local notation "W" => SmoothSite.mk (r ≫ t)
local notation "C" => pullback q r
local notation "G" => relativeGraphIdeal q r φ hφ
local notation "F" => divisorSheaf G
local notation "L" => tensorModules (tensorModules F T) N
local notation "LP" => tensorModules T N

variable (a : Γ(tensorModules F T, ⊤)) (b : Γ(T, ⊤)) (n d : Γ(N, ⊤))

local notation "s₀" => tensorSection (tensorModules F T) N ⊤
  (tensorSection F T ⊤ (divisorSheafGlobalSection G) b) d
local notation "s₁" => tensorSection (tensorModules F T) N ⊤ a n
local notation "pole" => tensorSection T N ⊤ b d
local notation "P" => zeroScheme C LP pole
local notation "A" => zeroScheme C (tensorModules F T) a
local notation "B" => zeroScheme C T b
local notation "NN" => zeroScheme C N n
local notation "D" => zeroScheme C N d
local notation "H₀" => zeroScheme C L s₀
local notation "H₁" => zeroScheme C L s₁
local notation "familySourceNative" => familySource (q ≫ t) (pullback.fst q r) L s₀ s₁ ≫
  (nativeParameterIso (.of k) U).inv
local notation "δ" => retainedPencilDifference t q r L LP s₀ s₁ pole
local notation "span[" I "]" => ofFiniteFlatSpan (X := U) (Y := W)
  ((I).subschemeι ≫ pullback.fst q r) ((I).subschemeι ≫ pullback.snd q r)
  (by simp only [Category.assoc, pullback.condition_assoc])

variable [IsFinite familySourceNative] [Flat familySourceNative]
  [IsFinite (P.subschemeι ≫ pullback.fst q r)] [Flat (P.subschemeι ≫ pullback.fst q r)]

/-- The zero endpoint is exactly the original graph after cancellation of the
same entire product pole, including every nonreduced multiplicity. -/
theorem retainedTensorDifference_zero
    (hb : IsEffectiveCartierDivisor B) (hd : IsEffectiveCartierDivisor D) :
    (graphFunctor k).map (nativeAffineSection (.of k) U 0) ≫ δ =
      (graphFunctor k).map (SmoothSite.homMk φ (by simp only [← Category.assoc, hφ])) := by
  haveI := nativeZeroSource_isFinite U (pullback.fst q r) L s₀ s₁
  haveI := nativeZeroSource_flat U (pullback.fst q r) L s₀ s₁
  haveI : IsFinite (G.subschemeι ≫ pullback.fst q r) := by
    rw [← relativeGraphSupportIso_hom_base]
    infer_instance
  haveI : Flat (G.subschemeι ≫ pullback.fst q r) := by
    rw [← relativeGraphSupportIso_hom_base]
    infer_instance
  let m := forgetBaseProductMap t q r
  haveI : IsFinite (G.subschemeι ≫ m ≫ pullback.fst (q ≫ t) (r ≫ t)) := by
    simpa only [m, forgetBaseProductMap_fst] using
      (inferInstance : IsFinite (G.subschemeι ≫ pullback.fst q r))
  haveI : Flat (G.subschemeι ≫ m ≫ pullback.fst (q ≫ t) (r ≫ t)) := by
    simpa only [m, forgetBaseProductMap_fst] using
      (inferInstance : Flat (G.subschemeι ≫ pullback.fst q r))
  haveI : IsFinite (P.subschemeι ≫ m ≫ pullback.fst (q ≫ t) (r ≫ t)) := by
    simpa only [m, forgetBaseProductMap_fst] using
      (inferInstance : IsFinite (P.subschemeι ≫ pullback.fst q r))
  haveI : Flat (P.subschemeι ≫ m ≫ pullback.fst (q ≫ t) (r ≫ t)) := by
    simpa only [m, forgetBaseProductMap_fst] using
      (inferInstance : Flat (P.subschemeι ≫ pullback.fst q r))
  haveI : IsFinite (H₀.subschemeι ≫ m ≫ pullback.fst (q ≫ t) (r ≫ t)) := by
    simpa only [m, forgetBaseProductMap_fst] using
      (inferInstance : IsFinite (H₀.subschemeι ≫ pullback.fst q r))
  haveI : Flat (H₀.subschemeι ≫ m ≫ pullback.fst (q ≫ t) (r ≫ t)) := by
    simpa only [m, forgetBaseProductMap_fst] using
      (inferInstance : Flat (H₀.subschemeι ≫ pullback.fst q r))
  rw [retainedPencilDifference_zero]
  calc span[H₀] - span[P] = span[G] := by
      simpa only [m, forgetBaseProductMap_fst, forgetBaseProductMap_snd] using
        ofFiniteFlatSpan_graph_tensor_poles_sub (X := U) (Y := W) m G T N b d hb hd
    _ = _ := ofFiniteFlatSpan_relativeGraph t q r φ hφ

variable [IsFinite (A.subschemeι ≫ pullback.fst q r)] [Flat (A.subschemeι ≫ pullback.fst q r)]
  [IsFinite (B.subschemeι ≫ pullback.fst q r)] [Flat (B.subschemeι ≫ pullback.fst q r)]
  [IsFinite (NN.subschemeι ≫ pullback.fst q r)] [Flat (NN.subschemeι ≫ pullback.fst q r)]
  [IsFinite (D.subschemeι ≫ pullback.fst q r)] [Flat (D.subschemeι ≫ pullback.fst q r)]

/-- The one endpoint has precisely the original signs on actual retained
whole zero-scheme spans. The numerator n occurs positively. -/
theorem retainedTensorDifference_one
    (hn : IsEffectiveCartierDivisor NN) (hd : IsEffectiveCartierDivisor D) :
    (graphFunctor k).map (nativeAffineSection (.of k) U 1) ≫ δ =
      (span[A] - span[B]) - (span[D] - span[NN]) := by
  haveI := nativeOneSource_isFinite U (pullback.fst q r) L s₀ s₁
  haveI := nativeOneSource_flat U (pullback.fst q r) L s₀ s₁
  let m := forgetBaseProductMap t q r
  have hf (I : C.IdealSheafData) [IsFinite (I.subschemeι ≫ pullback.fst q r)] :
      IsFinite (I.subschemeι ≫ m ≫ pullback.fst (q ≫ t) (r ≫ t)) := by
    simpa only [m, forgetBaseProductMap_fst] using
      (inferInstance : IsFinite (I.subschemeι ≫ pullback.fst q r))
  have hfl (I : C.IdealSheafData) [Flat (I.subschemeι ≫ pullback.fst q r)] :
      Flat (I.subschemeι ≫ m ≫ pullback.fst (q ≫ t) (r ≫ t)) := by
    simpa only [m, forgetBaseProductMap_fst] using
      (inferInstance : Flat (I.subschemeι ≫ pullback.fst q r))
  haveI := hf A
  haveI := hfl A
  haveI := hf B
  haveI := hfl B
  haveI := hf NN
  haveI := hfl NN
  haveI := hf D
  haveI := hfl D
  haveI := hf H₁
  haveI := hfl H₁
  haveI := hf P
  haveI := hfl P
  rw [retainedPencilDifference_one]
  simpa only [m, forgetBaseProductMap_fst, forgetBaseProductMap_snd] using
    ofFiniteFlatSpan_tensorProducts_sub (X := U) (Y := W) m
      (tensorModules F T) T N N a b n d hn hd

end AlgebraicGeometry.Cor
