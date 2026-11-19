/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Algebra.Homology.CochainComplex.Cousin
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.Filtration.Restriction
public import StacksFrontier.CategoryTheory.Abelian.SigmaExactness

/-! # The support tower on the Zariski opens of a smooth scheme -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme Opposite TopologicalSpace

universe u w w'

namespace AlgebraicGeometry.Gersten

open MotivicHomotopy SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [UnivLE.{u, w'}]

variable (X : SmoothSite (Spec (.of k))) (K : EffectiveMotivesMinus k)

local notation "O" => SmoothSite.opensFunctor X
set_option hygiene false in
set_option quotPrecheck false in
local notation "Ab" => AddCommGrpCat.{w'}
local notation "PSh" => X.left.Opensᵒᵖ ⥤ Ab

/-- The abelian structure on the transfer coefficients of the support tower. -/
local instance gerstenTowerAbelian : Abelian (LargeSheaves k) := SheafWithTransfers.abelian k

/-- The original closed-support colimits, with restriction along ambient opens. -/
def coniveauStagePresheaf (p : ℕ) (n : ℤ) : PSh where
  obj U := coniveauCohomology k ((O).obj U.unop) K n p
  map f := coniveauCohomologyOpenMap k X K n p f.unop
  map_id U := coniveauCohomologyOpenMap_id k X K n p U.unop
  map_comp f g := coniveauCohomologyOpenMap_comp k X K n p g.unop f.unop

/-- The adjacent relative support windows, with their actual open restrictions. -/
def coniveauWindowPresheaf (p : ℕ) (n : ℤ) : PSh where
  obj U := coniveauRelativeSupportCohomology k ((O).obj U.unop) K n p (p + 1)
  map f := coniveauRelativeSupportOpenMap k X K n p (p + 1) f.unop
  map_id U := coniveauRelativeSupportOpenMap_id k X K n p (p + 1) U.unop
  map_comp f g := coniveauRelativeSupportOpenMap_comp k X K n p (p + 1) g.unop f.unop

/-- The inclusion of supports of codimension at least `p + 1`. -/
def coniveauStageTransition (p : ℕ) (n : ℤ) :
    coniveauStagePresheaf k X K (p + 1) n ⟶ coniveauStagePresheaf k X K p n where
  app U := coniveauCohomologyTransition k ((O).obj U.unop) K n (Nat.le_succ _)
  naturality _ _ f := (coniveauCohomologyTransition_openMap_naturality
    k X K n (Nat.le_succ _) f.unop).symm

/-- The original restriction from a support stage to its relative window. -/
def coniveauStageToWindow (p : ℕ) (n : ℤ) :
    coniveauStagePresheaf k X K p n ⟶ coniveauWindowPresheaf k X K p n where
  app U := coniveauCohomologyToWindow k ((O).obj U.unop) K n p (p + 1)
  naturality _ _ f := (coniveauCohomologyToWindow_openMap_naturality
    k X K n p (p + 1) f.unop).symm

/-- The signed localization boundary from a window to the next support stage. -/
def coniveauWindowConnecting (p : ℕ) (n : ℤ) :
    coniveauWindowPresheaf k X K p n ⟶ coniveauStagePresheaf k X K (p + 1) (n + 1) where
  app U := coniveauWindowBoundary k ((O).obj U.unop) K n (Nat.le_succ _)
  naturality _ _ f := (coniveauWindowBoundary_openMap_naturality
    k X K n (Nat.le_succ _) f.unop).symm

/-- The adjacent support sequences assemble into the finite tower on the
smooth opens whenever the support windows are concentrated on the diagonal. -/
def coniveauExactSupportTower
    (h : ∀ (U : X.left.Opens) (p n : ℕ), p ≠ n →
      IsZero (coniveauRelativeSupportCohomology k ((O).obj U) K (n : ℤ) p (p + 1))) :
    ExactSupportTower PSh := by
  let b := SmoothSite.exists_nat_topologicalKrullDim_le k X
  let d := b.choose
  have hd : topologicalKrullDim X.left ≤ d := b.choose_spec
  refine
    { stage := fun p n ↦ coniveauStagePresheaf k X K p n
      layer := fun p n ↦ coniveauWindowPresheaf k X K p n
      transition := fun p n ↦ coniveauStageTransition k X K p n
      toLayer := fun p n ↦ coniveauStageToWindow k X K p n
      boundary := fun p n ↦ coniveauWindowConnecting k X K p n
      transition_toLayer_zero := ?_
      toLayer_boundary_zero := ?_
      boundary_transition_zero := ?_
      exact_stage := ?_
      exact_layer := ?_
      exact_boundary := ?_
      dimension := d
      isZero_stage := ?_
      isZero_off_diagonal := ?_ }
  · intro p n
    apply NatTrans.ext
    funext U
    exact coniveauCohomologyTransition_comp_toWindow k ((O).obj U.unop) K n (Nat.le_succ p)
  · intro p n
    apply NatTrans.ext
    funext U
    exact coniveauCohomologyToWindow_comp_boundary k ((O).obj U.unop) K n (Nat.le_succ p)
  · intro p n
    apply NatTrans.ext
    funext U
    exact coniveauWindowBoundary_comp_transition k ((O).obj U.unop) K n (Nat.le_succ p)
  · intro p n
    exact Stacks.SigmaExactness.exact_of_app _ (fun U ↦
      coniveauCohomologyStage_exact k ((O).obj U.unop) K n (Nat.le_succ p))
  · intro p n
    exact Stacks.SigmaExactness.exact_of_app _ (fun U ↦
      coniveauCohomologyWindow_exact k ((O).obj U.unop) K n (Nat.le_succ p))
  · intro p n
    exact Stacks.SigmaExactness.exact_of_app _ (fun U ↦
      coniveauWindowBoundary_exact k ((O).obj U.unop) K n (Nat.le_succ p))
  · intro p n hp
    apply (IsZero.iff_id_eq_zero _).2
    apply NatTrans.ext
    funext U
    have hU : topologicalKrullDim ((O).obj U.unop).left ≤ d :=
      Topology.IsEmbedding.subtypeVal.isInducing.topologicalKrullDim_le.trans hd
    exact (isZero_coniveauCohomology_above_dimension k ((O).obj U.unop) K n hU hp).eq_of_src _ _
  · intro p n hp
    apply (IsZero.iff_id_eq_zero _).2
    apply NatTrans.ext
    funext U
    exact (h U.unop p n hp).eq_of_src _ _

end AlgebraicGeometry.Gersten
