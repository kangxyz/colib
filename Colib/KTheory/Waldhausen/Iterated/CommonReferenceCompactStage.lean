/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceCompactLoopZero
public import Colib.KTheory.Waldhausen.Iterated.SimplexFamilyRealization

/-!
# Compact whole-nerve evaluation at every original iterated S-stage

Evaluation at a whole-nerve point factors through the actual compact carrier and recovers
exactly the old finite-simplex evaluation whenever the carrier point agrees.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology

universe u v

namespace CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve

open SmallWaldhausenCategory SSet

variable {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W)

/-- The native weak chain records the entire original reference diagram. -/
def chain {k : ℕ} (c : Fin (k + 1) ⥤ Codiscrete (Node F)) : ModelSimplex V W k where
  diagram := c ⋙ diagram F
  exact i := (c.obj i).as.1.hom.isExact
  zero i := (c.obj i).as.1.property
  weak _ _ f x := diagram_weak F (c.map f) x

/-- Reindexing restricts the same full chain, including its chosen node isomorphisms. -/
theorem chain_face {k l : ℕ} (c : Fin (k + 1) ⥤ Codiscrete (Node F)) (α : ⦋l⦌ ⟶ ⦋k⦌) :
    chain F (α.toOrderHom.monotone.functor ⋙ c) = (chain F c).face α := by
  apply ModelSimplex.ext_diagram
  rfl

/-- The actual common-reference nerve simplex represented by this undeformed chain. -/
def chainMap {k : ℕ} (c : Fin (k + 1) ⥤ Codiscrete (Node F)) :
    Δ[k] ⟶ nerve (Codiscrete (Node F)) :=
  SSet.yonedaEquiv.symm c

/-- Evaluate every original stage against all simplices of the same whole nerve. -/
def stageTransformation (r : ℕ) :
    (stages r).obj V ⊗ nerve (Codiscrete (Node F)) ⟶ (stages r).obj W where
  app n := ↾fun z ↦ stageSimplexFunction r (chain F z.2) n z.1 ⟨𝟙 n.unop⟩
  naturality n m α := by
    ext z : 3
    symm
    change ((stages r).obj W).map α
        (stageSimplexFunction r (chain F z.2) n z.1 ⟨𝟙 n.unop⟩) = _
    rw [stageSimplexFunction_naturality]
    change stageSimplexFunction r (chain F z.2) m
        (((stages r).obj V).map α z.1) ⟨α.unop ≫ 𝟙 n.unop⟩ =
      stageSimplexFunction r
        (chain F (α.unop.toOrderHom.monotone.functor ⋙ z.2)) m
        (((stages r).obj V).map α z.1) ⟨𝟙 m.unop⟩
    have h := stageSimplexFunction_face r (chain F z.2) α.unop m
      (((stages r).obj V).map α z.1) ⟨𝟙 m.unop⟩
    simpa only [Category.id_comp, Category.comp_id, ← chain_face] using h

/-- At the original stage zero this is the already constructed literal map. -/
theorem stageTransformation_zero : stageTransformation F 0 = stageZeroTransformation F := by
  ext n z : 3
  rfl

/-- The whole-nerve evaluation restricts to the unchanged entire finite-simplex family. -/
theorem stageTransformation_factorization (r : ℕ) {k : ℕ}
    (c : Fin (k + 1) ⥤ Codiscrete (Node F)) :
    (stages r).obj V ◁ chainMap F c ≫ stageTransformation F r =
      stageTransformationSimplex r (chain F c) := by
  ext n z : 4
  change stageSimplexFunction r (chain F ((chainMap F c).app n z.2))
      n z.1 ⟨𝟙 n.unop⟩ = stageSimplexFunction r (chain F c) n z.1 z.2
  have hc : chain F ((chainMap F c).app n z.2) = (chain F c).face z.2.down :=
    chain_face F c z.2.down
  rw [hc]
  have h := stageSimplexFunction_face r (chain F c) z.2.down n z.1 ⟨𝟙 n.unop⟩
  have he : (⟨𝟙 n.unop ≫ z.2.down⟩ : (Δ[k] : SSet.{u}).obj n) = z.2 := by
    apply ULift.ext
    exact Category.id_comp _
  rw [he] at h
  exact h.symm

/-- Every actual nerve point is represented by a full original finite chain. -/
theorem exists_chain (y : |nerve (Codiscrete (Node F))|) :
    ∃ (k : ℕ) (c : Fin (k + 1) ⥤ Codiscrete (Node F)) (z : |(Δ[k] : SSet.{u})|),
      SSet.toTop.map (chainMap F c) z = y := by
  obtain ⟨n, f, t, ht⟩ := realization_exists_simplex y
  cases n using SimplexCategory.rec with
  | _ k =>
    refine ⟨k, SSet.yonedaEquiv f, t, ?_⟩
    change SSet.toTop.map (SSet.yonedaEquiv.symm (SSet.yonedaEquiv f)) t = y
    rw [Equiv.symm_apply_apply]
    exact ht

variable {T U : Type v} [TopologicalSpace T] [TopologicalSpace U]
  [CompactSpace T] [CompactSpace U]

/-- Compact stage evaluation uses exactly the original compact carrier. -/
def compactStageFamily (r : ℕ) (p : C(T, |nerve (Codiscrete (Node F))|)) :
    C(T × stageSpace r V, stageSpace r W) :=
  SSet.ProductRealization.compactRightEvaluation (stageTransformation F r) p

/-- The original stage-zero evaluation is unchanged. -/
theorem compactStageFamily_zero (p : C(T, |nerve (Codiscrete (Node F))|)) :
    compactStageFamily F 0 p = compactStageZeroFamily F p := by
  unfold compactStageFamily compactStageZeroFamily
  rw [stageTransformation_zero]

/-- Matching the actual nerve point recovers the whole original realized simplex family. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/CommonReferenceNerveCompactStage.lean:136-151"
  "adaptation" "The original finite simplex is recovered at a matching compact nerve point."]
theorem compactStageFamily_eq_chain (r : ℕ) (p : C(T, |nerve (Codiscrete (Node F))|))
    {k : ℕ} (c : Fin (k + 1) ⥤ Codiscrete (Node F))
    (t : T) (z : |(Δ[k] : SSet.{u})|) (h : SSet.toTop.map (chainMap F c) z = p t)
    (x : stageSpace r V) :
    compactStageFamily F r p (t, x) = stageSimplexRealization r (chain F c) (x, z) := by
  let q := (realizationProductSimplexIso ((stages r).obj V) k).inv (x, z)
  have hc := ConcreteCategory.congr_hom
    (prodComparison_natural_whiskerLeft (A := (stages r).obj V) SSet.toTop (chainMap F c)) q
  change SSet.ProductRealization.comparison ((stages r).obj V) _
      (SSet.toTop.map ((stages r).obj V ◁ chainMap F c) q) =
    ((realizationProductSimplexIso ((stages r).obj V) k).hom q).map id
      (SSet.toTop.map (chainMap F c)) at hc
  change _ = ((realizationProductSimplexIso ((stages r).obj V) k).hom
    ((realizationProductSimplexIso ((stages r).obj V) k).inv (x, z))).map id
      (SSet.toTop.map (chainMap F c)) at hc
  rw [Iso.inv_hom_id_apply] at hc
  have he := SSet.ProductRealization.compactRightEvaluation_eq_of_comparison
    (stageTransformation F r) p t x (SSet.toTop.map ((stages r).obj V ◁ chainMap F c) q)
    (hc.trans (_root_.Prod.ext rfl h))
  change compactStageFamily F r p (t, x) = _ at he
  refine he.trans ?_
  change (SSet.toTop.map ((stages r).obj V ◁ chainMap F c) ≫
    SSet.toTop.map (stageTransformation F r)) q = _
  rw [← Functor.map_comp, stageTransformation_factorization]
  rfl

/-- Exact equality of compact parameter points identifies their stage evaluations. -/
theorem compactStageFamily_of_point_eq (r : ℕ)
    (p : C(T, |nerve (Codiscrete (Node F))|))
    (q : C(U, |nerve (Codiscrete (Node F))|)) (t : T) (s : U) (h : p t = q s)
    (x : stageSpace r V) : compactStageFamily F r p (t, x) = compactStageFamily F r q (s, x) :=
  SSet.ProductRealization.compactRightEvaluation_eq_of_parameter
    (stageTransformation F r) p q t s h x

end CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve
