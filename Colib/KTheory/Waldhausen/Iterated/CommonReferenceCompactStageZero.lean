/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.CategoryTheory.Waldhausen.SConstruction.NerveSimplexFamily
public import Colib.KTheory.Waldhausen.Iterated.Prespectrum
public import Colib.Topology.ClassifyingSpace.Contraction
public import Colib.Topology.Realization.ProductCompactEvaluation
public import Mathlib.CategoryTheory.CodiscreteCategory

/-!
# Compact common-reference evaluation at the original Waldhausen stage zero

The carrier is the actual codiscrete nerve of zero-preserving exact maps with a fixed reference
isomorphism. Evaluation retains the entire original S-simplex of the input and the unchanged
parameter point, including compact parameters that meet several finite simplices.
-/
@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits MonoidalCategory
open scoped Simplicial Topology

universe u v

namespace CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve

open SmallWaldhausenCategory

variable {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W)

/-- Nodes retain the original exact map and the whole specified reference isomorphism. -/
abbrev Node := Σ G : V ⟶ W, F.hom.toFunctor ≅ G.hom.toFunctor

/-- Nerve arrows use the actual composition through the fixed reference. -/
def diagram : Codiscrete (Node F) ⥤ (V.obj.Obj ⥤ W.obj.Obj) where
  obj i := i.as.1.hom.toFunctor
  map {i j} _ := i.as.2.inv ≫ j.as.2.hom
  map_id i := by simp
  map_comp f g := by simp [Category.assoc]

/-- The reference itself, with its unchanged identity isomorphism, is a carrier node. -/
def referenceNode : Codiscrete (Node F) := ⟨⟨F, Iso.refl F.hom.toFunctor⟩⟩

/-- The contraction uses the canonical point of the same actual nerve realization. -/
def referenceContraction :
    (ContinuousMap.const |nerve (Codiscrete (Node F))|
      (classifyingSpacePoint (referenceNode F))).Homotopy
      (ContinuousMap.id |nerve (Codiscrete (Node F))|) :=
  classifyingSpaceInitialContraction (IsInitial.ofUnique (referenceNode F))

/-- Each nerve-chain edge is the composite of the specified natural isomorphisms. -/
theorem diagram_weak {i j : Codiscrete (Node F)} (f : i ⟶ j) (x : V.obj.Obj) :
    W.obj.waldhausen.weq (((diagram F).map f).app x) := by
  apply W.obj.waldhausen.weq_iso
  change IsIso ((i.as.2.inv ≫ j.as.2.hom).app x)
  infer_instance

/-- Evaluate an original stage-zero grid against the unchanged chain of reference maps. -/
def stageZeroTransformation :
    (stages 0).obj V ⊗ nerve (Codiscrete (Node F)) ⟶ (stages 0).obj W where
  app n := ↾fun z ↦
    (weakNaturalTransformationSimplex V.obj.waldhausen W.obj.waldhausen
      (z.2 ⋙ diagram F)
      (fun i ↦ (z.2.obj i).as.1.hom.isExact)
      (fun _ _ f x ↦ diagram_weak F (z.2.map f) x)).app n (z.1, ⟨𝟙 n.unop⟩)
  naturality n m α := by
    ext z : 3
    symm
    let φ := weakNaturalTransformationSimplex V.obj.waldhausen W.obj.waldhausen
      (z.2 ⋙ diagram F)
      (fun i ↦ (z.2.obj i).as.1.hom.isExact)
      (fun _ _ f x ↦ diagram_weak F (z.2.map f) x)
    let A := (stages 0).obj V ⊗ Δ[n.unop.len]
    let B := (stages 0).obj W
    let p : A.obj n := (z.1, ⟨𝟙 n.unop⟩)
    have hn := congrArg (fun g : A.obj n ⟶ B.obj m ↦ g p) (φ.naturality α)
    change B.map α (φ.app n p) = _
    refine (show B.map α (φ.app n p) = φ.app m (A.map α p) from hn.symm).trans ?_
    let A' := (stages 0).obj V ⊗ Δ[m.unop.len]
    let q : A'.obj m := (((stages 0).obj V).map α z.1, ⟨𝟙 m.unop⟩)
    have h := congrArg (fun a : A' ⟶ B ↦ a.app m q)
      (weakNaturalTransformationSimplex_face V.obj.waldhausen W.obj.waldhausen
        (z.2 ⋙ diagram F)
        (fun i ↦ (z.2.obj i).as.1.hom.isExact)
        (fun _ _ f x ↦ diagram_weak F (z.2.map f) x) α.unop)
    have hstd : (SSet.stdSimplex.map α.unop).app m (ULift.up (𝟙 m.unop)) =
        (SSet.stdSimplex.obj n.unop).map α (ULift.up (𝟙 n.unop)) := by
      change ULift.up (𝟙 m.unop ≫ α.unop) = ULift.up (α.unop ≫ 𝟙 n.unop)
      simp
    have he := congrArg (fun t ↦ φ.app m (((stages 0).obj V).map α z.1, t)) hstd.symm
    exact he.trans h

variable {T U : Type v} [TopologicalSpace T] [TopologicalSpace U]
  [CompactSpace T] [CompactSpace U]

/-- Evaluate at every point of the actual compact reference parameter and original stage zero. -/
def compactStageZeroFamily (p : C(T, |nerve (Codiscrete (Node F))|)) :
    C(T × stageSpace 0 V, stageSpace 0 W) :=
  SSet.ProductRealization.compactRightEvaluation (stageZeroTransformation F) p

/-- Two instances of the same actual carrier point evaluate identically. -/
theorem compactStageZeroFamily_of_point_eq
    (p : C(T, |nerve (Codiscrete (Node F))|))
    (q : C(U, |nerve (Codiscrete (Node F))|)) (t : T) (s : U) (h : p t = q s)
    (x : stageSpace 0 V) :
    compactStageZeroFamily F p (t, x) = compactStageZeroFamily F q (s, x) :=
  SSet.ProductRealization.compactRightEvaluation_eq_of_parameter
    (stageZeroTransformation F) p q t s h x

end CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve
