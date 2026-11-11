/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.CorestrictionPoints

/-!
# Towers of diagonal corestrictions

The actual scalar projections compose before passing to signed cycles. Native
finite pushforward composes with its residue degrees, giving the tower and
identity laws on the original diagonal groups.

Adapted from `Motivic/Cohomology/Diagonal/CorestrictionTower.lean:45-114` at
`a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u w

namespace AlgebraicGeometry.MotivicCohomology.DiagonalCorestriction

open _root_.AlgebraicGeometry.Scheme SmoothSite
open PresheafWithTransfers
open DiagonalTopDegree DiagonalCycleSymbols
open DiagonalFiniteCyclePushforward (scalarMap multiplicativeGroupMap torusMap torusMap_isPullback)
open DiagonalReducedPushforward (torusMap_coordinate torusMap_coordinate_assoc)
open DiagonalReducedPushforward (torusPower_left_hom_ext)

section Tower

variable {k L E : Type u} [Field k] [Field L] [Field E]
  [Algebra k L] [Algebra L E] [Algebra k E] [IsScalarTower k L E]

private theorem scalarMap_comp :
    scalarMap (k := L) (E := E) ≫ scalarMap (k := k) (E := L) =
      scalarMap (k := k) (E := E) := by
  rw [← Spec.map_comp]
  exact congrArg (fun f : k →+* E => Spec.map (CommRingCat.ofHom f))
    (IsScalarTower.algebraMap_eq k L E).symm

private theorem multiplicativeGroupMap_comp :
    multiplicativeGroupMap (k := L) (E := E) ≫ multiplicativeGroupMap (k := k) (E := L) =
      multiplicativeGroupMap (k := k) (E := E) := by
  let p := multiplicativeGroupULift ↘ Spec (.of (ULift.{u} ℤ))
  let b (F : Type u) [Field F] := specULiftZIsTerminal.from (Spec (.of F))
  have h₁ {A B : Type u} [Field A] [Field B] [Algebra A B] :
      multiplicativeGroupMap (k := A) (E := B) ≫ pullback.fst p (b A) =
        pullback.fst p (b B) := pullback.lift_fst _ _ _
  have h₂ {A B : Type u} [Field A] [Field B] [Algebra A B] :
      multiplicativeGroupMap (k := A) (E := B) ≫ pullback.snd p (b A) =
        pullback.snd p (b B) ≫ scalarMap (k := A) (E := B) := pullback.lift_snd _ _ _
  apply pullback.hom_ext (f := p) (g := b k)
  · simp only [Category.assoc, h₁]
  · simp only [Category.assoc, h₂, reassoc_of% h₂, scalarMap_comp]

/-- The scalar projection of the ordered torus power composes along the actual field tower. -/
theorem torusMap_comp (q : ℕ) :
    torusMap (k := L) (E := E) q ≫ torusMap (k := k) (E := L) q =
      torusMap (k := k) (E := E) q := by
  apply torusPower_left_hom_ext q
  · simp only [Category.assoc, (torusMap_isPullback q).w,
      reassoc_of% (torusMap_isPullback q).w, scalarMap_comp]
  · intro i
    simp only [Category.assoc, torusMap_coordinate, torusMap_coordinate_assoc,
      multiplicativeGroupMap_comp]

private theorem pointAmbientMap_comp (q : ℕ) :
    pointAmbientMap (k := L) (E := E) q ≫ pointAmbientMap (k := k) (E := L) q =
      pointAmbientMap (k := k) (E := E) q := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pointAmbientMap_fst, pointAmbientMap_fst_assoc, scalarMap_comp]
  · simp only [Category.assoc, pointAmbientMap_snd, pointAmbientMap_snd_assoc, torusMap_comp]

variable [Module.Finite k L] [Module.Finite L E] [Module.Finite k E]

/-- Native finite pushforward of point cycles composes with all original image degrees. -/
theorem pointPushforward_comp (q : ℕ) :
    (pointPushforward (k := k) (E := L) q).comp
      (pointPushforward (k := L) (E := E) q) = pointPushforward (k := k) (E := E) q := by
  apply AddMonoidHom.ext
  intro α
  apply Subtype.ext
  simp only [AddMonoidHom.comp_apply, pointPushforward_val, finiteCyclePushforward_comp_apply]
  have h (f g : pointAmbient E q ⟶ pointAmbient k q)
      [IsFinite f] [IsFinite g] (e : f = g) :
      finiteCyclePushforward f α.val = finiteCyclePushforward g α.val := by
    cases e
    rfl
  exact h _ _ (pointAmbientMap_comp q)

/-- Actual raw diagonal corestriction composes along every finite field tower. -/
@[colib_ref "motivic_source_a6805c4" "Motivic/Cohomology/Diagonal/CorestrictionTower.lean:55-65"
  "adaptation" "Tower law for the actual finite diagonal pushforward"]
theorem corestriction_comp (q : ℕ) :
    (corestriction (k := k) (E := L) q).comp (corestriction (k := L) (E := E) q) =
      corestriction (k := k) (E := E) q := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨α, rfl⟩ := cycleClass_surjective E q x
  simp only [AddMonoidHom.comp_apply, corestriction_cycleClass]
  exact congrArg (cycleClass k q)
    (DFunLike.congr_fun (pointPushforward_comp (k := k) (L := L) (E := E) q) α)

variable [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of L))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of E))) AddCommGrpCat.{u + 1})]

/-- The derived diagonal transfer retains the same finite-field tower. -/
theorem integralCorestriction_comp (q : ℕ) :
    (integralCorestriction (k := k) (E := L) q).comp
      (integralCorestriction (k := L) (E := E) q) = integralCorestriction (k := k) (E := E) q := by
  apply AddMonoidHom.ext
  intro x
  apply (motivicRawBaseEvaluationComparison k q q).injective
  simp only [AddMonoidHom.comp_apply, integralCorestriction_comparison]
  exact DFunLike.congr_fun (corestriction_comp (k := k) (L := L) (E := E) q)
    (motivicRawBaseEvaluationComparison E q q x)

end Tower

section Identity

variable (k : Type u) [Field k]

private theorem scalarMap_id : scalarMap (k := k) (E := k) = 𝟙 _ :=
  Spec.map_id _

private theorem multiplicativeGroupMap_id :
    multiplicativeGroupMap (k := k) (E := k) = 𝟙 _ := by
  let p := multiplicativeGroupULift ↘ Spec (.of (ULift.{u} ℤ))
  let b := specULiftZIsTerminal.from (Spec (.of k))
  apply pullback.hom_ext (f := p) (g := b)
  · rw [Category.id_comp]
    exact pullback.lift_fst _ _ _
  · rw [Category.id_comp]
    exact (pullback.lift_snd _ _ _).trans
      ((congrArg (pullback.snd p b ≫ ·) (scalarMap_id k)).trans (Category.comp_id _))

/-- The torus projection for the identity scalar extension is the identity. -/
theorem torusMap_id (q : ℕ) : torusMap (k := k) (E := k) q = 𝟙 _ := by
  apply torusPower_left_hom_ext q
  · rw [Category.id_comp, (torusMap_isPullback q).w, scalarMap_id]
    exact Category.comp_id _
  · intro i
    rw [Category.id_comp, torusMap_coordinate, multiplicativeGroupMap_id, Category.comp_id]

private theorem pointAmbientMap_id (q : ℕ) : pointAmbientMap (k := k) (E := k) q = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [pointAmbientMap_fst, scalarMap_id, Category.id_comp]
    exact Category.comp_id _
  · simp only [pointAmbientMap_snd, torusMap_id, Category.id_comp]
    exact Category.comp_id _

/-- Identity scalar extension is the identity on actual signed point cycles. -/
theorem pointPushforward_id (q : ℕ) :
    pointPushforward (k := k) (E := k) q = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro α
  apply Subtype.ext
  rw [pointPushforward_val]
  have h (f : pointAmbient k q ⟶ pointAmbient k q) [IsFinite f] (e : f = 𝟙 _) :
      finiteCyclePushforward f α.val = α.val := by
    subst f
    exact finiteCyclePushforward_id _
  exact h _ (pointAmbientMap_id k q)

/-- Identity scalar extension acts identically on the original raw diagonal group. -/
theorem corestriction_id (q : ℕ) :
    corestriction (k := k) (E := k) q = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨α, rfl⟩ := cycleClass_surjective k q x
  rw [corestriction_cycleClass, pointPushforward_id]
  rfl

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Identity scalar extension acts identically on the original derived diagonal group. -/
theorem integralCorestriction_id (q : ℕ) :
    integralCorestriction (k := k) (E := k) q = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro x
  apply (motivicRawBaseEvaluationComparison k q q).injective
  rw [integralCorestriction_comparison, corestriction_id]
  rfl

end Identity

end AlgebraicGeometry.MotivicCohomology.DiagonalCorestriction
