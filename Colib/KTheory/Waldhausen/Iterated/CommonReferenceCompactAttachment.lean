/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceCompactPrespectrum

/-!
# Exact evaluation of compact common-reference postcomposition

Attaching the actual postcomposed node retains its full specified isomorphism to the new
reference. The common reanchoring cancels in every edge of the diagram. The evaluated
compact family is the actual postcomposition, with no change of time or input.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology

universe u v

namespace CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve

open SmallWaldhausenCategory SSet

variable {V W Z : WideSubcategory preservesZero.{u}} (F : V ⟶ W) (J : W ⟶ Z) (G : V ⟶ Z)
  (ε : G.hom.toFunctor ≅ (F ≫ J).hom.toFunctor)

/-- Actual postcomposition and reanchoring on the original dependent node. -/
def attachPostcompNode (N : Node F) : Node G :=
  ⟨N.1 ≫ J, ε ≪≫ isoWhiskerRight N.2 J.hom.toFunctor⟩

/-- The original nerve map induced by the specified attachment. -/
def attachPostcompNerve : nerve (Codiscrete (Node F)) ⟶ nerve (Codiscrete (Node G)) :=
  nerveMap (Codiscrete.functorOfFun (attachPostcompNode F J G ε))

/-- This same map acts continuously on the complete actual carrier. -/
def attachPostcompParameter : C(|nerve (Codiscrete (Node F))|, |nerve (Codiscrete (Node G))|) :=
  (SSet.toTop.map (attachPostcompNerve F J G ε)).hom

/-- The common reanchor cancels in all arrows, retaining the actual postcomposition. -/
theorem chain_attachPostcomp {k : ℕ} (c : Fin (k + 1) ⥤ Codiscrete (Node F)) :
    chain G (c ⋙ Codiscrete.functorOfFun (attachPostcompNode F J G ε)) =
      (chain F c).postcomp J := by
  apply ModelSimplex.ext_diagram
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro i j f
  ext X
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  let a := J.hom.toFunctor.map ((c.obj i).as.2.inv.app X)
  let b := J.hom.toFunctor.map ((c.obj j).as.2.hom.app X)
  calc
    _ = (a ≫ ε.inv.app X) ≫ (ε.hom.app X ≫ b) := rfl
    _ = a ≫ b := by rw [Category.assoc, Iso.inv_hom_id_app_assoc]

/-- The exact simplicial square holds at every original stage. -/
theorem stageTransformation_attachPostcomp (r : ℕ) :
    (stages r).obj V ◁ attachPostcompNerve F J G ε ≫ stageTransformation G r =
      stageTransformation F r ≫ (stages r).map J := by
  ext n z : 4
  change stageSimplexFunction r
      (chain G (z.2 ⋙ Codiscrete.functorOfFun (attachPostcompNode F J G ε)))
      n z.1 ⟨𝟙 n.unop⟩ =
    ((stages r).map J).app n (stageSimplexFunction r (chain F z.2) n z.1 ⟨𝟙 n.unop⟩)
  rw [chain_attachPostcomp]
  exact stageSimplexFunction_postcomp r (chain F z.2) J n z.1 ⟨𝟙 n.unop⟩

variable {S : Type v} [TopologicalSpace S] [CompactSpace S]

/-- The compact stage family retains the exact evaluation pair under attachment. -/
theorem compactStageFamily_attachPostcomp (r : ℕ)
    (p : C(S, |nerve (Codiscrete (Node F))|)) (t : S) (x : stageSpace r V) :
    compactStageFamily G r ((attachPostcompParameter F J G ε).comp p) (t, x) =
      SSet.toTop.map ((stages r).map J) (compactStageFamily F r p (t, x)) := by
  let L := SSet.ProductRealization.compactRightLift (X := (stages r).obj V) p
  let q := L (t, x)
  let ι := attachPostcompNerve F J G ε
  have hc := ConcreteCategory.congr_hom
    (prodComparison_natural_whiskerLeft (A := (stages r).obj V) SSet.toTop ι) q
  change SSet.ProductRealization.comparison ((stages r).obj V) _
      (SSet.toTop.map ((stages r).obj V ◁ ι) q) =
    (SSet.ProductRealization.comparison ((stages r).obj V) _ q).map id
      (SSet.toTop.map ι) at hc
  rw [show SSet.ProductRealization.comparison ((stages r).obj V) _ q = (x, p t) from
    SSet.ProductRealization.comparison_compactRightLift p t x] at hc
  have h := SSet.ProductRealization.compactRightEvaluation_eq_of_comparison
    (stageTransformation G r) ((attachPostcompParameter F J G ε).comp p) t x
    (SSet.toTop.map ((stages r).obj V ◁ ι) q) hc
  change compactStageFamily G r ((attachPostcompParameter F J G ε).comp p) (t, x) = _ at h
  refine h.trans ?_
  change (SSet.toTop.map ((stages r).obj V ◁ attachPostcompNerve F J G ε) ≫
    SSet.toTop.map (stageTransformation G r)) q =
      (SSet.toTop.map (stageTransformation F r) ≫ SSet.toTop.map ((stages r).map J)) q
  rw [← Functor.map_comp, ← Functor.map_comp, stageTransformation_attachPostcomp]

/-- Every original level, including the unchanged original input-loop coordinate. -/
theorem compactPrespectrumFamily_attachPostcomp
    (p : C(S, |nerve (Codiscrete (Node F))|)) (n : ℕ) (t : S)
    (x : (prespectrum V).space n) :
    compactPrespectrumFamily G ((attachPostcompParameter F J G ε).comp p) n (t, x) =
      (prespectrumMap J).map n (compactPrespectrumFamily F p n (t, x)) := by
  cases n with
  | zero =>
    change Path (stagePoint 0 V) (stagePoint 0 V) at x
    apply Path.ext
    funext s
    have h := compactStageFamily_attachPostcomp F J G ε 0 p t (x s)
    rw [compactStageFamily_zero, compactStageFamily_zero] at h
    exact h
  | succ r => exact compactStageFamily_attachPostcomp F J G ε r p t x

/-- Equality of the entire continuous family, not just of its designated faces. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/CommonReferenceNerveCompactAttachment.lean:74-83"
  "adaptation" "Exact joint postcomposition and reanchoring on the original compact family."]
theorem compactPrespectrumFamily_attachPostcomp_map
    (p : C(S, |nerve (Codiscrete (Node F))|)) (n : ℕ) :
    compactPrespectrumFamily G ((attachPostcompParameter F J G ε).comp p) n =
      ((prespectrumMap J).map n).comp (compactPrespectrumFamily F p n) := by
  apply ContinuousMap.ext
  rintro ⟨t, x⟩
  exact compactPrespectrumFamily_attachPostcomp F J G ε p n t x

end CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve
