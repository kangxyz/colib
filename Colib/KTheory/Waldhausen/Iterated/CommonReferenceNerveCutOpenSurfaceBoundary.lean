/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNerveCutOpenRelativeExtension

/-!
# Six compatible carrier faces from two whole route surfaces

The left and right surfaces agree with common start and finish paths and preserve the
two distinct carrier tips. The twelve whole edge equations follow from these identities.
The original native pointwise formulas give the two recovered routes on the glued
boundary. This does not construct either route surface.

Adapted from `CommonReferenceNerveCutOpenSurfaceBoundary.lean` in Quillen K-theory at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u

namespace CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve.CutOpenCarrier
open SmallWaldhausenCategory Topology.SimplexCubeExtension

variable {V W T : WideSubcategory preservesZero.{u}} (F : V ⟶ W) (J : W ⟶ T)
  (G : V ⟶ T) (ε₀ ε₁ : G.hom.toFunctor ≅ (F ≫ J).hom.toFunctor)

/-- Two complete route surfaces share whole endpoint paths and retain separate seed tips. -/
structure RouteSurfaces where
  /-- The left route surface, with route time first and seed time second. -/
  left : C(I × I, space F J G ε₀ ε₁)
  /-- The right route surface, with route time first and seed time second. -/
  right : C(I × I, space F J G ε₀ ε₁)
  /-- The shared seed path at route time zero. -/
  start : C(I, space F J G ε₀ ε₁)
  /-- The shared seed path at route time one. -/
  finish : C(I, space F J G ε₀ ε₁)
  left_start (t : I) : left (0, t) = start t
  left_finish (t : I) : left (1, t) = finish t
  right_start (t : I) : right (0, t) = start t
  right_finish (t : I) : right (1, t) = finish t
  left_zero (s : I) : left (s, 0) = tipMinus F J G ε₀ ε₁
  left_one (s : I) : left (s, 1) = tipPlus F J G ε₀ ε₁
  right_zero (s : I) : right (s, 0) = tipMinus F J G ε₀ ε₁
  right_one (s : I) : right (s, 1) = tipPlus F J G ε₀ ε₁

namespace RouteSurfaces
variable {F J G ε₀ ε₁} (S : RouteSurfaces F J G ε₀ ε₁)

/-- The two route surfaces, fixed endpoint paths, and separate constant tip faces. -/
def faces (a : Fin 3 × Bool) : C(face a, space F J G ε₀ ε₁) :=
  if a.1 = 0 then
    ⟨fun z ↦ (if a.2 then S.right else S.left) (z.val.val 1, z.val.val 2), by
      exact (if a.2 then S.right else S.left).continuous.comp
        (((continuous_apply 1).comp (continuous_subtype_val.comp continuous_subtype_val)).prodMk
          ((continuous_apply 2).comp (continuous_subtype_val.comp continuous_subtype_val)))⟩
  else if a.1 = 1 then
    ⟨fun z ↦ (if a.2 then S.finish else S.start) (z.val.val 2), by
      exact (if a.2 then S.finish else S.start).continuous.comp
        ((continuous_apply 2).comp (continuous_subtype_val.comp continuous_subtype_val))⟩
  else ContinuousMap.const _ (if a.2 then tipPlus F J G ε₀ ε₁ else tipMinus F J G ε₀ ε₁)

/-- All twelve whole edges agree; endpoint-path tip values follow from the left surface. -/
theorem compatible : EdgeCompatible (fun a ↦ S.faces a) := by
  have hs0 : S.start 0 = tipMinus F J G ε₀ ε₁ :=
    (S.left_start 0).symm.trans (S.left_zero 0)
  have hs1 : S.start 1 = tipPlus F J G ε₀ ε₁ :=
    (S.left_start 1).symm.trans (S.left_one 0)
  have hf0 : S.finish 0 = tipMinus F J G ε₀ ε₁ :=
    (S.left_finish 0).symm.trans (S.left_zero 1)
  have hf1 : S.finish 1 = tipPlus F J G ε₀ ε₁ :=
    (S.left_finish 1).symm.trans (S.left_one 1)
  intro i j hij a b x hi hj
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals
    cases a <;> cases b <;>
      simp only [face, Set.mem_ofPred_eq, endpoint, Bool.false_eq_true, ↓reduceIte] at hj
  all_goals
    dsimp [faces]
    first
    | change x.val (1 : Fin 3) = _ at hj
    | change x.val (2 : Fin 3) = _ at hj
    rw [hj]
    first
    | exact S.left_start _
    | exact S.left_finish _
    | exact S.right_start _
    | exact S.right_finish _
    | exact S.left_zero _
    | exact S.left_one _
    | exact S.right_zero _
    | exact S.right_one _
    | exact hs0
    | exact hs1
    | exact hf0
    | exact hf1

/-- Build the legitimate six-face boundary without requiring any interior homotopy. -/
def boundary : RelativeBoundary F J G ε₀ ε₁ where
  faces := S.faces
  compatible := S.compatible
  start := S.start
  finish := S.finish
  route_zero z := by simp [faces]
  route_one z := by simp [faces]
  seed_zero z := by simp [faces]
  seed_one z := by simp [faces]


/-- Ordinary pointwise whole-route identities supply the two native face recovery fields. -/
theorem recoversRoutes
    {f g : prespectrum V ⟶ parameterLooping (nativeCone J)}
    (H K : Homotopy f g)
    (hl : ∀ (n : ℕ) (s t : I) (x : (prespectrum V).space n),
      nativeEval F J G ε₀ ε₁ n (S.left (s, t)) x =
        Path.toContinuousMap (H.level n (s, x)) t)
    (hr : ∀ (n : ℕ) (s t : I) (x : (prespectrum V).space n),
      nativeEval F J G ε₀ ε₁ n (S.right (s, t)) x =
        Path.toContinuousMap (K.level n (s, x)) t) :
    S.boundary.RecoversRoutes H K where
  left z n x := hl n (z.val.val 1) (z.val.val 2) x
  right z n x := hr n (z.val.val 1) (z.val.val 2) x

end RouteSurfaces
end CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve.CutOpenCarrier
