/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Colib.KTheory.Waldhausen.Iterated.CommonReferenceNerveCutOpenRelativeExtension

/-!
# Relative comparison after an actual native cone map

The six original cut-open carrier faces retain their full boundary. Only their native images
under a supplied prespectrum map need recover the two original routes. Compact evaluation,
loop currying, and postcomposition preserve all three times and the independent structure time.
No interior comparison or replacement of the original routes is assumed.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Waldhausen Topology.LoopPrespectrum Topology
open scoped Topology unitInterval
universe u
namespace CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve.CutOpenCarrier.RelativeBoundary
open SimplexCubeExtension
variable {V W T : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}}
  {F : V ⟶ W} {J : W ⟶ T} {G : V ⟶ T}
  {ε₀ ε₁ : G.hom.toFunctor ≅ (F ≫ J).hom.toFunctor}
  (B : RelativeBoundary F J G ε₀ ε₁)
  {P : LoopPrespectrum.{u}} (j : nativeCone J ⟶ P)

/-- The compact loop family followed by the actual prescribed cone map. -/
def mappedLoops (n : ℕ) : C((unitInterval × unitInterval) × (prespectrum V).space n,
    (parameterLooping P).space n) :=
  ((parameterLoopingMap j).map n).comp (B.loops n)

/-- The original seed time remains independent of both comparison coordinates. -/
theorem mappedLoops_apply (n : ℕ) (r s t : unitInterval) (x : (prespectrum V).space n) :
    Path.toContinuousMap (B.mappedLoops j n ((r, s), x)) t =
      j.map n (nativeEval F J G ε₀ ε₁ n (B.carrier ((r, s), t)) x) := rfl

variable {f g : prespectrum V ⟶ parameterLooping P} (H K : Homotopy f g)

/-- Only the images of the two complete outer faces are required to be the chosen routes. -/
structure RecoversMappedRoutes : Prop where
  left (z : face (0, false)) (n : ℕ) (x : (prespectrum V).space n) :
    j.map n (nativeEval F J G ε₀ ε₁ n (B.faces (0, false) z) x) =
      Path.toContinuousMap (H.level n (z.val.val 1, x)) (z.val.val 2)
  right (z : face (0, true)) (n : ℕ) (x : (prespectrum V).space n) :
    j.map n (nativeEval F J G ε₀ ε₁ n (B.faces (0, true) z) x) =
      Path.toContinuousMap (K.level n (z.val.val 1, x)) (z.val.val 2)

variable (h : B.RecoversMappedRoutes j H K)

/-- The mapped whole initial face is the actual original first route. -/
theorem mappedLoops_left (h : B.RecoversMappedRoutes j H K)
    (n : ℕ) (s : unitInterval) (x : (prespectrum V).space n) :
    B.mappedLoops j n ((0, s), x) = H.level n (s, x) := by
  apply Path.ext
  funext t
  exact (congrArg (fun y ↦ j.map n (nativeEval F J G ε₀ ε₁ n y x))
    (B.extension_face (0, false) (onFace (0, false) (coordinates 0 s t) rfl))).trans
      (h.left _ n x)

/-- The mapped whole terminal face is the actual original second route. -/
theorem mappedLoops_right (h : B.RecoversMappedRoutes j H K)
    (n : ℕ) (s : unitInterval) (x : (prespectrum V).space n) :
    B.mappedLoops j n ((1, s), x) = K.level n (s, x) := by
  apply Path.ext
  funext t
  exact (congrArg (fun y ↦ j.map n (nativeEval F J G ε₀ ε₁ n y x))
    (B.extension_face (0, true) (onFace (0, true) (coordinates 1 s t) rfl))).trans
      (h.right _ n x)

/-- The six prescribed carrier faces produce a relative comparison of the mapped whole routes. -/
def mappedRelativeComparison (h : B.RecoversMappedRoutes j H K) : H.RelHomotopy K where
  level n :=
    { toFun z := B.mappedLoops j n ((z.1, z.2.1), z.2.2)
      continuous_toFun := by fun_prop
      map_zero_left z := B.mappedLoops_left j H K h n z.1 z.2
      map_one_left z := B.mappedLoops_right j H K h n z.1 z.2
      prop' r z hz := by
        change B.mappedLoops j n ((r, z.1), z.2) = H.level n (z.1, z.2)
        rcases hz with hz | hz | hz
        · rcases z with ⟨s, x⟩
          dsimp at hz
          subst s
          refine Eq.trans ?_ (B.mappedLoops_left j H K h n 0 x)
          apply Path.ext
          funext t
          exact congrArg (fun y ↦ j.map n (nativeEval F J G ε₀ ε₁ n y x))
            ((B.carrier_start r t).trans (B.carrier_start 0 t).symm)
        · rcases z with ⟨s, x⟩
          dsimp at hz
          subst s
          refine Eq.trans ?_ (B.mappedLoops_left j H K h n 1 x)
          apply Path.ext
          funext t
          exact congrArg (fun y ↦ j.map n (nativeEval F J G ε₀ ε₁ n y x))
            ((B.carrier_finish r t).trans (B.carrier_finish 0 t).symm)
        · rw [hz, H.at_point]
          apply Path.ext
          funext t
          exact (congrArg (j.map n)
            (nativeEval_point F J G ε₀ ε₁ n (B.carrier ((r, z.1), t)))).trans
              (j.map_point n) }
  comm n r s x t := by
    apply Path.ext
    funext v
    exact (congrArg (j.map (n + 1))
      (nativeEval_structure F J G ε₀ ε₁ n (B.carrier ((r, s), v)) x t)).trans
        (congrArg (fun p ↦ p t)
          (j.comm n (nativeEval F J G ε₀ ε₁ n (B.carrier ((r, s), v)) x)))

/-- The comparison uses the unchanged chosen extension and the actual postmap at every time. -/
theorem mappedRelativeComparison_apply (n : ℕ) (r s t : unitInterval)
    (x : (prespectrum V).space n) :
    Path.toContinuousMap ((B.mappedRelativeComparison j H K h).level n (r, (s, x))) t =
      j.map n (nativeEval F J G ε₀ ε₁ n (B.carrier ((r, s), t)) x) := rfl

end CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve.CutOpenCarrier.RelativeBoundary
