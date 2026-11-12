/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.OpenSupportedPushforward
public import Colib.AlgebraicGeometry.Chow.NoetherianPushforward
public import Colib.AlgebraicGeometry.Correspondences.Moving.PrincipalOrder
public import Colib.AlgebraicGeometry.Correspondences.Divisors.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.StalkTransport
public import StacksFrontier.AlgebraicGeometry.Chow.RationalFunctions.OpenImmersion

/-! # Principal correspondence through the actual retained map

The outer retained map is arbitrary. Only each original support inclusion is a
closed immersion. Its degree one cancels in the tower formula; the outer map's
actual residue degree is retained, together with image collisions and signs.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Stacks.Chow TopologicalSpace
open Function.locallyFinsuppWithin
universe u
namespace AlgebraicGeometry.AlgebraicCycle

/-- Reuse the retained-support decomposition with the identity map, then apply the
actual weighted pushforward. No finiteness or immersion condition on `m` is needed. -/
theorem noetherianCyclePushforward_eq_sum_of_retained_points
    {C V T : Scheme.{u}} [IsNoetherian C] [IsNoetherian V]
    (j : V ⟶ C) [IsOpenImmersion j] (m : V ⟶ T)
    (c : AlgebraicCycle C ℤ) (d : AlgebraicCycle V ℤ)
    (h : ∀ y : V, d y = c (j y))
    (l : (Function.locallyFinsupp.finite_support c).toFinset → V)
    (hl : ∀ z, j (l z) = z.val) :
    noetherianCyclePushforward m d =
      ∑ z : (Function.locallyFinsupp.finite_support c).toFinset,
        single (m (l z)) (c z.val * (m.residueDegree (l z) : ℤ)) := by
  have hd := finiteCyclePushforward_eq_sum_of_retained_points j (𝟙 V) c d h l hl
  simp only [finiteCyclePushforward_id, Scheme.Hom.id_apply] at hd
  rw [hd, map_sum]
  apply Finset.sum_congr rfl
  intro z _
  exact noetherianCyclePushforward_single m (l z) (c z.val)

end AlgebraicGeometry.AlgebraicCycle
namespace AlgebraicGeometry.Cor.PrincipalOrder
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X Y : SmoothSite (Spec (.of k))} [IsAffine X.left]
  {C V : Scheme.{u}} [IsIntegral C] [IsNoetherian C] [V.IsQuasiAffine]
  (q : C ⟶ X.left) [IsProper q] (j : V ⟶ C) [IsOpenImmersion j]
  [SmoothOfRelativeDimension 1 (j ≫ q)]
  (W : C.Opens) [Nonempty W] (hW : (Set.range j)ᶜ ⊆ (W : Set C))
  (r : Γ(C, W)) (hr : IsUnit r)
  (g : V ⟶ Y.left) (hbase : j ≫ q ≫ X.hom = g ≫ Y.hom)
  [IsIntegral V] [IsNoetherian V]

local instance retainedOpen_dominant : IsDominant j :=
  ((tfae_isDominant_of_isIntegral j).out 1 2).mpr (genericPoint_eq_of_isOpenImmersion j)

/-- The original principal correspondence is the weighted pushforward along the
actual retained structure map, without imposing a closed immersion on that map. -/
theorem correspondence_val_eq_noetherianPushforward
    (m : V ⟶ pullback X.hom Y.hom)
    (h₁ : m ≫ pullback.fst X.hom Y.hom = j ≫ q)
    (h₂ : m ≫ pullback.snd X.hom Y.hom = g) :
    (correspondence q j W hW r hr g hbase).val =
      noetherianCyclePushforward m (principalCycle V
        (dominantFunctionFieldMap j (C.germToFunctionField W r))) := by
  classical
  let c := principalCycle C (C.germToFunctionField W r)
  let d := principalCycle V (dominantFunctionFieldMap j (C.germToFunctionField W r))
  let s := Function.locallyFinsupp.finite_support c
  let l (z : s.toFinset) := supportPoint j W hW r hr z.val (s.mem_toFinset.mp z.property)
  have hcoeff (z : V) : d z = c (j z) :=
    ord_dominantFunctionFieldMap_of_isOpenImmersion j (C.germToFunctionField W r) z
  have hl (z : s.toFinset) : j (l z) = z.val :=
    supportPoint_image j W hW r hr _ _
  change _ = noetherianCyclePushforward m d
  rw [correspondence_val_sum,
    AlgebraicCycle.noetherianCyclePushforward_eq_sum_of_retained_points j m c d hcoeff l hl]
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
  have hdegree : a.residueDegree η = m.residueDegree (i η) := by
    rw [ha, residueDegree_comp, residueDegree_eq_one_of_isPreimmersion i η, mul_one]
  rw [supportCorrespondence_val_eq_single]
  change single (a η) (c z.val * (a.residueDegree η : ℤ)) =
    single (m (i η)) (c z.val * (m.residueDegree (i η) : ℤ))
  rw [hdegree]
  exact congrArg (fun t : (integralComponentAt z.val).subscheme ⟶ pullback X.hom Y.hom =>
    single (t η) (c z.val * (m.residueDegree (i η) : ℤ))) ha

/-- The same dense-open unit gives the actual retained principal Weil divisor.
The supplied `hF` identifies its original representative, not a cycle comparison. -/
theorem correspondence_val_eq_pushforward_principalDivisor
    (W : DenseOpen C) [Nonempty W.val]
    (hW : (Set.range j)ᶜ ⊆ (W.val : Set C)) (u : Γ(C, W.val)ˣ)
    (F : (rationalFunctions C)ˣ)
    (hF : Units.map (ofSectionRingHom C W).toMonoidHom u = F)
    (m : V ⟶ pullback X.hom Y.hom)
    (h₁ : m ≫ pullback.fst X.hom Y.hom = j ≫ q)
    (h₂ : m ≫ pullback.snd X.hom Y.hom = g) :
    (correspondence q j W.val hW u.val u.isUnit g hbase).val =
      WeilDivisor.pushforwardCycle m
        (principalDivisor V (rationalFunctionsUnitsMulEquivOfOpenImmersion j F)) := by
  rw [correspondence_val_eq_noetherianPushforward q j W.val hW u.val u.isUnit g hbase m h₁ h₂]
  change noetherianCyclePushforward m _ =
    noetherianCyclePushforward m (WeilDivisor.toAlgebraicCycle _)
  rw [WeilDivisor.toAlgebraicCycle_principalDivisor,
    rationalFunctionsUnitsMulEquivOfOpenImmersion_coe,
    rationalFunctionsEquivFunctionField_rationalFunctionsRingEquivOfOpenImmersion,
    functionFieldEquiv_openImmersion_eq_dominantFunctionFieldMap]
  have hrep : (rationalFunctionsEquivFunctionField C).val F.val =
      C.germToFunctionField W.val u.val := by
    have hh := congrArg Units.val hF
    change (ofSectionRingHom C W) u.val = F.val at hh
    rw [ofSectionRingHom_apply] at hh
    rw [← hh]
    exact (rationalFunctionsEquivFunctionField C).property W u.val
      (((genericPoint_spec C).mem_open_set_iff W.val.isOpen).mpr
        (by simpa using ‹Nonempty W.val›))
  rw [hrep]

end AlgebraicGeometry.Cor.PrincipalOrder
