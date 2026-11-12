/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.OpenSupportedPushforward
public import Colib.AlgebraicGeometry.Correspondences.Graph.TargetPushforward
public import Colib.AlgebraicGeometry.Correspondences.Moving.PrincipalOrder
public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.StalkTransport

/-! # The original principal correspondence in the retained product -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Stacks.Chow
open Function.locallyFinsuppWithin

universe u

namespace AlgebraicGeometry.Cor.PrincipalOrder

open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X Y : SmoothSite (Spec (.of k))} [IsAffine X.left]
  {C V : Scheme.{u}} [IsIntegral C] [IsNoetherian C] [V.IsQuasiAffine]
  (q : C ⟶ X.left) [IsProper q] (j : V ⟶ C) [IsOpenImmersion j]
  [SmoothOfRelativeDimension 1 (j ≫ q)]
  (W : C.Opens) [Nonempty W] (hW : (Set.range j)ᶜ ⊆ (W : Set C))
  (r : Γ(C, W)) (hr : IsUnit r)
  (g : V ⟶ Y.left) (hbase : j ≫ q ≫ X.hom = g ≫ Y.hom)

set_option quotPrecheck false in
local notation "c" => principalCycle C (C.germToFunctionField W r)

/-- The original correspondence vanishes when its entire retained scheme is empty. -/
theorem correspondence_eq_zero_of_isEmpty [IsEmpty V] :
    correspondence q j W hW r hr g hbase = 0 := by
  apply Subtype.ext
  rw [correspondence_val_sum]
  let h := Function.locallyFinsupp.finite_support c
  let : IsEmpty h.toFinset :=
    ⟨fun z => isEmptyElim (supportPoint j W hW r hr z.val (h.mem_toFinset.mp z.property))⟩
  exact Finset.sum_of_isEmpty _

/-- Postcomposing with an original graph preserves all support degrees and
the original signed principal correspondence. -/
theorem correspondence_comp_graph {Z : SmoothSite (Spec (.of k))} (u : Y ⟶ Z)
    (g' : V ⟶ Z.left) (hg : g ≫ u.left = g')
    (hbase' : j ≫ q ≫ X.hom = g' ≫ Z.hom) :
    correspondence q j W hW r hr g hbase ≫ (graphFunctor k).map u =
      correspondence q j W hW r hr g' hbase' := by
  classical
  apply Subtype.ext
  rw [correspondence_val_sum]
  unfold correspondence
  rw [Preadditive.sum_comp]
  change (finiteCorrespondences X.hom Z.hom).subtype _ = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro z _
  let hz : c z.val ≠ 0 := (Function.locallyFinsupp.finite_support c).mem_toFinset.mp z.property
  let m := supportMap q j W hW r hr g hbase z.val hz
  let m' := supportMap q j W hW r hr g' hbase' z.val hz
  let : IsIntegral (integralComponentAt z.val).subscheme := isIntegral_integralComponentAt z.val
  let η := genericPoint (integralComponentAt z.val).subscheme
  let hm := supportMap_isAdmissible q j W hW r hr g hbase z.val hz
  have hmap : m ≫ graphTargetMap k X u = m' := by
    apply pullback.hom_ext
    · simp only [Category.assoc, graphTargetMap_fst, m, m', supportMap_fst]
    · simp only [Category.assoc, graphTargetMap_snd, m, m', supportMap_snd,
        supportMap_snd_assoc, hg]
  rw [supportCorrespondence_val_eq_single]
  change (incidenceTorPairing X.hom Y.hom Z.hom
    (singleFiniteCorrespondence X.hom Y.hom (m η) hm (c z.val * (m.residueDegree η : ℤ)))
    (graphCorrespondenceOfComponents Y.hom Z.hom u.left (MorphismProperty.Over.w u)
      (finite_genericPoints k (Cor.mk Y)))).val =
    single (m' η) (c z.val * (m'.residueDegree η : ℤ))
  rw [incidenceTorPairing_finiteImage_single_graph_right_val X.hom Y.hom Z.hom u.left
    (MorphismProperty.Over.w u) (finite_genericPoints k (Cor.mk Y)) m m' hmap η hm (c z.val)]
  exact finiteCyclePushforward_single m' η (c z.val)

variable [IsIntegral V] [IsNoetherian V]

local instance retainedOpen_isDominant : IsDominant j :=
  ((tfae_isDominant_of_isIntegral j).out 1 2).mpr (genericPoint_eq_of_isOpenImmersion j)

/-- With a closed retained structure graph, the original correspondence is
the native pushforward of the same principal divisor on that retained open. -/
theorem correspondence_val_eq_pushforward_of_closed
    (m : V ⟶ pullback X.hom Y.hom) [IsClosedImmersion m]
    (h₁ : m ≫ pullback.fst X.hom Y.hom = j ≫ q)
    (h₂ : m ≫ pullback.snd X.hom Y.hom = g) :
    (correspondence q j W hW r hr g hbase).val =
      finiteCyclePushforward m (principalCycle V
        (dominantFunctionFieldMap j (C.germToFunctionField W r))) := by
  classical
  let d := principalCycle V (dominantFunctionFieldMap j (C.germToFunctionField W r))
  let s := Function.locallyFinsupp.finite_support c
  let l (z : s.toFinset) := supportPoint j W hW r hr z.val (s.mem_toFinset.mp z.property)
  have hcoeff (z : V) : d z = c (j z) :=
    ord_dominantFunctionFieldMap_of_isOpenImmersion j (C.germToFunctionField W r) z
  have hl (z : s.toFinset) : j (l z) = z.val :=
    supportPoint_image j W hW r hr _ _
  change _ = finiteCyclePushforward m d
  rw [correspondence_val_sum,
    AlgebraicCycle.finiteCyclePushforward_eq_sum_of_retained_points j m c d hcoeff l hl]
  apply Finset.sum_congr rfl
  intro z _
  let hz : c z.val ≠ 0 := s.mem_toFinset.mp z.property
  let i := supportLift j W hW r hr z.val hz
  let a := supportMap q j W hW r hr g hbase z.val hz
  let : IsIntegral (integralComponentAt z.val).subscheme := isIntegral_integralComponentAt z.val
  let η := genericPoint (integralComponentAt z.val).subscheme
  have ha : a = i ≫ m := by
    apply pullback.hom_ext
    · simp only [a, i, Category.assoc, supportMap_fst, h₁, supportLift_comp_assoc]
    · simp only [a, i, Category.assoc, supportMap_snd, h₂]
  let : IsClosedImmersion a := ha.symm ▸ inferInstanceAs (IsClosedImmersion (i ≫ m))
  rw [supportCorrespondence_val_eq_single]
  change single (a η) (c z.val * (a.residueDegree η : ℤ)) = single (m (i η)) (c z.val)
  rw [residueDegree_eq_one_of_isPreimmersion, Nat.cast_one, mul_one]
  exact congrArg (fun t : (integralComponentAt z.val).subscheme ⟶ pullback X.hom Y.hom =>
    single (t η) (c z.val)) ha

include hW hr hbase in
/-- The native correspondence with the retained principal cycle as its closed image. -/
theorem exists_correspondence_with_closed_value
    (m : V ⟶ pullback X.hom Y.hom) [IsClosedImmersion m]
    (h₁ : m ≫ pullback.fst X.hom Y.hom = j ≫ q)
    (h₂ : m ≫ pullback.snd X.hom Y.hom = g) :
    ∃ α : Cor.mk X ⟶ Cor.mk Y, α.val =
      finiteCyclePushforward m (principalCycle V
        (dominantFunctionFieldMap j (C.germToFunctionField W r))) :=
  ⟨correspondence q j W hW r hr g hbase,
    correspondence_val_eq_pushforward_of_closed q j W hW r hr g hbase m h₁ h₂⟩

end AlgebraicGeometry.Cor.PrincipalOrder
