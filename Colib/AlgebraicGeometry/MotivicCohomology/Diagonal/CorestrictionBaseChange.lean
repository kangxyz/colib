/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.FiniteFlatBaseChange
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.FieldChangeCycleGrades
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.ProperPushforward

/-!
# Scalar extension of a transferred finite point

Scalar extension keeps the entire pullback of the original finite point,
with its scheme structure and all local lengths. The Cartesian projections
are those of the original point-times-torus ambient scheme.

Adapted from `Motivic/Cohomology/Diagonal/CorestrictionBaseChange.lean:36-258`
at `a6805c4a87cdfd7717dd7a94039246a167f15380`, using the native Stacks
flat change of Chow base and its finite pushforward square.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalCorestrictionBaseChange

open _root_.AlgebraicGeometry.Scheme
open DiagonalCorestriction DiagonalTopDegree DiagonalFieldChange
open DiagonalFiniteCyclePushforward (scalarMap)

section FiniteBaseChange

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {X X' P P' : Scheme.{u}}
  {s : X ⟶ Spec (.of k)} {s' : X' ⟶ Spec (.of L)}
  [LocallyOfFiniteType s] [LocallyOfFiniteType s']
  {p : X' ⟶ X} (sq : IsPullback p s' s (scalarMap (k := k) (E := L)))

/-- Changing from the chosen pullback to the actual Cartesian square transports the cycle
by the original inverse comparison isomorphism. -/
theorem val_baseChangeCyclePullbackOfIsPullback (d : ℤ)
    (α : CycleGroup (fieldChowSituation k) s d) :
    (baseChangeCyclePullbackOfIsPullback (fieldExtensionBaseChangeSituation k L) rfl
        s sq d α).val =
      finiteCyclePushforward sq.isoPullback.inv
        (baseChangeCyclePullback (fieldExtensionBaseChangeSituation k L) s d α).val := by
  apply Function.locallyFinsuppWithin.ext
  intro x
  rw [baseChangeCyclePullbackOfIsPullback_apply]
  have h := finiteCyclePushforward_apply_of_isClosedImmersion sq.isoPullback.inv
    (baseChangeCyclePullback (fieldExtensionBaseChangeSituation k L) s d α).val
    (sq.isoPullback.hom x)
  have hx : sq.isoPullback.inv (sq.isoPullback.hom x) = x :=
    congrArg (fun f : X' ⟶ X' => f x) sq.isoPullback.hom_inv_id
  rw [hx] at h
  exact h.symm

variable {f : P ⟶ X} {f' : P' ⟶ X'} {v : P' ⟶ P}
  [IsFinite f] [IsFinite f'] (sf : IsPullback v f' f p)

/-- Native finite pushforward and scalar pullback commute on the actual Cartesian square. -/
@[stacks 0FVL "Finite proper pushforward read in the native ungraded cycles"]
theorem finiteCyclePushforward_baseChangeCyclePullback (d : ℤ)
    (α : CycleGroup (fieldChowSituation k) (f ≫ s) d) :
    finiteCyclePushforward f'
      (baseChangeCyclePullbackOfIsPullback (fieldExtensionBaseChangeSituation k L) rfl
        (f ≫ s) (sf.paste_vert sq) d α).val =
      (baseChangeCyclePullbackOfIsPullback (fieldExtensionBaseChangeSituation k L) rfl s sq d
        (properPushforward (fieldChowSituation k) (f ≫ s) s f rfl d α)).val := by
  let B := fieldExtensionBaseChangeSituation k L
  let sqP := sf.paste_vert sq
  let bc := baseChangeMorphism B s f
  let : IsFinite bc :=
    MorphismProperty.of_isPullback (isPullback_baseChangeMorphism B s f)
      (inferInstance : IsFinite f)
  have H := congrArg Subtype.val (properPushforward_baseChangeCyclePullback B s f d α)
  rw [properPushforward_val_eq_finiteCyclePushforward] at H
  have hcomp : sqP.isoPullback.inv ≫ f' = bc ≫ sq.isoPullback.inv := by
    apply sq.hom_ext
    · simp only [Category.assoc, IsPullback.isoPullback_inv_fst, ← sf.w,
        IsPullback.isoPullback_inv_fst_assoc, bc]
      exact (baseChangeMorphism_comp_fst B s f).symm
    · simp only [Category.assoc, IsPullback.isoPullback_inv_snd, bc]
      exact (baseChangeMorphism_comp_snd B s f).symm
  rw [val_baseChangeCyclePullbackOfIsPullback, val_baseChangeCyclePullbackOfIsPullback,
    finiteCyclePushforward_comp_apply]
  change finiteCyclePushforward (sqP.isoPullback.inv ≫ f') _ = _
  rw [finiteCyclePushforward_congr_map _ _ hcomp, ← finiteCyclePushforward_comp_apply]
  exact congrArg (finiteCyclePushforward sq.isoPullback.inv) H

end FiniteBaseChange

section WholePoint

variable {k E L : Type u} [Field k] [Field E] [Field L] [Algebra k E] [Algebra k L]

private theorem val_baseChange_finite_fundamental
    {P P' : Scheme.{u}} [IsNoetherian P'] (sP : P ⟶ Spec (.of k))
    (sP' : P' ⟶ Spec (.of L)) [IsFinite sP] [IsFinite sP'] {v : P' ⟶ P}
    (sqP : IsPullback v sP' sP (scalarMap (k := k) (E := L))) :
    (baseChangeCyclePullbackOfIsPullback (fieldExtensionBaseChangeSituation k L) rfl sP sqP 0
      (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sP (𝟙 P) 0)).val =
      AlgebraicCycle.fundamentalCycle P' := by
  let B := fieldExtensionBaseChangeSituation k L
  let i : (pullback (𝟙 P) v : Scheme.{u}) ⟶ P' := pullback.snd (𝟙 P) v
  let : IsIso i := inferInstanceAs (IsIso (pullback.snd (𝟙 P) v))
  let : IsFinite (𝟙 P ≫ sP) := inferInstance
  let : IsFinite (𝟙 P' ≫ sP') := inferInstance
  have hdim := schemeDeltaDimension_le_zero_of_finite_closedSupport k sP (𝟙 P)
  have h := baseChangeCyclePullbackOfIsPullback_cycleAssociatedToClosedSubscheme B rfl
    sP sqP (𝟙 P) 0 hdim
  have h' := cycleAssociatedToClosedSubscheme_eq_of_iso B.baseChange sP'
    i (𝟙 P') (asIso i) (Category.comp_id i) 0
  have hv := congrArg (fun c : CycleGroup (fieldChowSituation L) sP' 0 => c.val) (h.trans h')
  exact hv.trans ((val_gradeZero_finite_closedSupport L sP' (𝟙 P')).trans
    (finiteCyclePushforward_id _))

/-- The full scalar fiber of the original extension field. -/
abbrev changedPointSupport : Scheme.{u} :=
  pullback (scalarMap (k := k) (E := E)) (scalarMap (k := k) (E := L))

variable (q : ℕ)
  (f : SmoothSite.base (Spec (.of E)) ⟶ SmoothSite.torusPower (Spec (.of E)) q)

/-- The full scalar fiber maps to the original changed torus ambient. -/
def changedPointMap : changedPointSupport (k := k) (E := E) (L := L) ⟶ pointAmbient L q :=
  (pointAmbientMap_isPullback (k := k) (L := L) q).lift
    (pullback.fst _ _ ≫ finitePointMap (k := k) q f) (pullback.snd _ _) (by
      rw [Category.assoc, finitePointMap_fst]
      exact pullback.condition)

/-- The whole changed point retains its original map after projection. -/
@[reassoc (attr := simp)]
theorem changedPointMap_original :
    changedPointMap (k := k) (L := L) q f ≫ pointAmbientMap (k := k) (E := L) q =
      pullback.fst _ _ ≫ finitePointMap (k := k) q f :=
  IsPullback.lift_fst _ _ _ _

/-- The whole changed point retains the actual new scalar projection. -/
@[reassoc (attr := simp)]
theorem changedPointMap_base :
    changedPointMap (k := k) (L := L) q f ≫ pointAmbientStructure L q = pullback.snd _ _ :=
  IsPullback.lift_snd _ _ _ _

/-- The square of the original and scalar-extended finite points is Cartesian. -/
theorem changedPointMap_isPullback :
    IsPullback (pullback.fst (scalarMap (k := k) (E := E)) (scalarMap (k := k) (E := L)))
      (changedPointMap (k := k) (L := L) q f) (finitePointMap (k := k) q f)
      (pointAmbientMap (k := k) (E := L) q) := by
  apply IsPullback.of_bot (t := pointAmbientMap_isPullback (k := k) (L := L) q)
  · rw [changedPointMap_base, finitePointMap_fst]
    exact IsPullback.of_hasPullback _ _
  · exact (changedPointMap_original q f).symm

variable [Module.Finite k E]

instance changedPointMap_isFinite : IsFinite (changedPointMap (k := k) (L := L) q f) :=
  MorphismProperty.of_isPullback (changedPointMap_isPullback q f)
    (inferInstance : IsFinite (finitePointMap (k := k) q f))

instance changedPointSupport_isNoetherian :
    IsNoetherian (changedPointSupport (k := k) (E := E) (L := L)) := by
  let s := scalarMap (k := k) (E := E)
  let : IsFinite s := (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  exact isNoetherian_of_quasiCompact_locallyOfFiniteType
    (pullback.snd s (scalarMap (k := k) (E := L)))

/-- Restricting a transferred graph is the finite pushforward of the whole changed point. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/Diagonal/CorestrictionBaseChange.lean:239-261"
  "adaptation" "Scalar change preserves the full finite-point pushforward and its multiplicities"]
theorem pointPushforward_graph_fieldChange_val :
    (pointCycleFieldChange (k := k) (L := L) q
      (pointPushforward (k := k) q ((Cor.graphFunctor E).map f))).val =
      finiteCyclePushforward (changedPointMap (k := k) (L := L) q f)
        (AlgebraicCycle.fundamentalCycle (changedPointSupport (k := k) (E := E) (L := L))) := by
  let B := fieldExtensionBaseChangeSituation k L
  let s := pointAmbientStructure k q
  let s' := pointAmbientStructure L q
  let m := finitePointMap (k := k) (E := E) q f
  let m' := changedPointMap (k := k) (E := E) (L := L) q f
  let v := pullback.fst (scalarMap (k := k) (E := E)) (scalarMap (k := k) (E := L))
  let sq := pointAmbientMap_isPullback (k := k) (L := L) q
  let sf := changedPointMap_isPullback (k := k) (E := E) (L := L) q f
  let : IsFinite (scalarMap (k := k) (E := E)) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  let : IsFinite (m ≫ s) := by
    have hm : m ≫ s = scalarMap (k := k) (E := E) := finitePointMap_fst (k := k) (E := E) q f
    rw [hm]
    infer_instance
  let : IsFinite (m' ≫ s') := by
    have hm' : m' ≫ s' =
        pullback.snd (scalarMap (k := k) (E := E)) (scalarMap (k := k) (E := L)) :=
      changedPointMap_base (k := k) (E := E) (L := L) q f
    rw [hm']
    infer_instance
  let : IsFinite (𝟙 (Spec (.of E)) ≫ (m ≫ s)) := inferInstance
  let α : CycleGroup (fieldChowSituation k) (m ≫ s) 0 :=
    cycleAssociatedToClosedSubscheme (fieldChowSituation k) (m ≫ s) (𝟙 (Spec (.of E))) 0
  let β : point k ⟶ DiagonalCycleSymbols.target k q :=
    pointPushforward (k := k) (E := E) q ((Cor.graphFunctor E).map f)
  have hα : α.val = AlgebraicCycle.fundamentalCycle (Spec (.of E)) :=
    (val_gradeZero_finite_closedSupport k (m ≫ s) (𝟙 (Spec (.of E)))).trans
      (finiteCyclePushforward_id _)
  have hβ : β.val = finiteCyclePushforward m (AlgebraicCycle.fundamentalCycle (Spec (.of E))) :=
    pointPushforward_graph_fundamental (k := k) (E := E) q f
  have hg : pointCycleGrade k q β =
      properPushforward (fieldChowSituation k) (m ≫ s) s m rfl 0 α := by
    apply Subtype.ext
    change β.val = _
    have h := properPushforward_val_eq_finiteCyclePushforward
      (fieldChowSituation k) (m ≫ s) s m rfl 0 α
    exact hβ.trans ((congrArg (finiteCyclePushforward m) hα).symm.trans h.symm)
  have hα' := val_baseChange_finite_fundamental (k := k) (L := L) (m ≫ s) (m' ≫ s')
    (sf.paste_vert sq)
  have hswap := finiteCyclePushforward_baseChangeCyclePullback
    (k := k) (L := L) (s := s) (s' := s') (f := m) (f' := m') (v := v) sq sf 0 α
  have hchange := pointCycleFieldChange_val (k := k) (L := L) q β
  apply Function.locallyFinsuppWithin.ext
  intro y
  let eval (c : AlgebraicCycle (pointAmbient L q) ℤ) : ℤ := c y
  refine (congrArg eval hchange).trans ?_
  refine (congrArg (fun c : CycleGroup (fieldChowSituation k) s 0 =>
    (baseChangeCyclePullbackOfIsPullback B rfl s sq 0 c).val y) hg).trans ?_
  refine (congrArg eval hswap.symm).trans ?_
  exact congrArg (fun c : AlgebraicCycle (changedPointSupport (k := k) (E := E) (L := L)) ℤ =>
    finiteCyclePushforward m' c y) hα'

end WholePoint

end AlgebraicGeometry.MotivicCohomology.DiagonalCorestrictionBaseChange
