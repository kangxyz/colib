/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References
public import Colib.Topology.HomotopyFiber.BasedLESNaturality
public import Mathlib.Algebra.FiveLemma

/-!
# Finite detection of the target map from the actual fiber ladder

The original five-term homotopy-fiber sequence detects a target map in degree n+2.
Only the stated neighboring degrees of the source and actual fiber map are used.
No stable equivalence, connectivity at other points, or identification of spectrum
structure maps is assumed.
-/
/-! Implementation provenance:
`Quillen/Topology/HomotopyFiber/FiniteTargetDetection.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original chosen points, finite ranges,
actual maps, signed indices and proof strategy are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology
universe u
namespace Topology.HomotopyFiber
variable {X Y A B : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace A] [TopologicalSpace B]
  {f : C(X, A)} {g : C(Y, B)} (p : C(X, Y)) (q : C(A, B))
  (sq : q.comp f = g.comp p) (x : X) (a : A) (h : f x = a)

/-- The precise four neighboring group maps detect the original target in degree n+2. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyFiber/FiniteTargetDetection.lean:32"
  "adaptation" "Original finite-range ladder and stable proper-row roof."]
theorem piMap_target_bijective_of_fiberMap (n : ℕ)
    (hfhi : Function.Surjective (HomotopyGroup.piMap (n + 1) (map p q sq a)
      (map_basepoint p q sq x a h)))
    (hphi : Function.Bijective (HomotopyGroup.piMap (n + 1) p (x := x) rfl))
    (hflo : Function.Bijective (HomotopyGroup.piMap n (map p q sq a)
      (map_basepoint p q sq x a h)))
    (hplo : Function.Injective (HomotopyGroup.piMap n p (x := x) rfl)) :
    Function.Bijective (HomotopyGroup.piMap (n + 1) q (x := a) rfl) := by
  let h' : g (p x) = q a :=
    (ContinuousMap.congr_fun sq x).symm.trans (congrArg q h)
  refine MonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (HomotopyGroup.piMap (n + 1) (projection f a) (projection_basepoint f a x h))
    (HomotopyGroup.piMap (n + 1) f h) (connectingHom f a x h n)
    (HomotopyGroup.piMap n (projection f a) (projection_basepoint f a x h))
    (HomotopyGroup.piMap (n + 1) (projection g (q a)) (projection_basepoint g (q a) (p x) h'))
    (HomotopyGroup.piMap (n + 1) g h') (connectingHom g (q a) (p x) h' n)
    (HomotopyGroup.piMap n (projection g (q a)) (projection_basepoint g (q a) (p x) h'))
    (HomotopyGroup.piMap (n + 1) (map p q sq a) (map_basepoint p q sq x a h))
    (HomotopyGroup.piMap (n + 1) p rfl) (HomotopyGroup.piMap (n + 1) q rfl)
    (HomotopyGroup.piMap n (map p q sq a) (map_basepoint p q sq x a h))
    (HomotopyGroup.piMap n p rfl) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hfhi hphi hflo hplo
  · exact (projectionHom_natural p q sq x a h (n + 1)).symm
  · exact (originalHom_natural p q sq x a h (n + 1)).symm
  · exact (connectingHom_natural p q sq x a h n).symm
  · exact (projectionHom_natural p q sq x a h n).symm
  · exact MonoidHom.mulExact_iff.mpr (piMap_range_projection_eq_ker f a x h (n + 1)).symm
  · exact MonoidHom.mulExact_iff.mpr (range_piMap_eq_ker_connectingHom f a x h n).symm
  · exact MonoidHom.mulExact_iff.mpr (range_connectingHom_eq_ker_projection f a x h n).symm
  · exact MonoidHom.mulExact_iff.mpr
      (piMap_range_projection_eq_ker g (q a) (p x) h' (n + 1)).symm
  · exact MonoidHom.mulExact_iff.mpr (range_piMap_eq_ker_connectingHom g (q a) (p x) h' n).symm
  · exact MonoidHom.mulExact_iff.mpr (range_connectingHom_eq_ker_projection g (q a) (p x) h' n).symm

/-- The same finite ladder retains explicitly specified source and target basepoints. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyFiber/FiniteTargetDetection.lean:66"
  "adaptation" "Original finite-range ladder and stable proper-row roof."]
theorem piMap_target_bijective_of_basedFiberMap (y : Y) (b : B)
    (h' : g y = b) (hx : p x = y) (ha : q a = b) (n : ℕ)
    (hfhi : Function.Surjective (HomotopyGroup.piMap (n + 1) (mapAt p q sq a b ha)
      (mapAt_basepoint p q sq x a y b h h' hx ha)))
    (hphi : Function.Bijective (HomotopyGroup.piMap (n + 1) p hx))
    (hflo : Function.Bijective (HomotopyGroup.piMap n (mapAt p q sq a b ha)
      (mapAt_basepoint p q sq x a y b h h' hx ha)))
    (hplo : Function.Injective (HomotopyGroup.piMap n p hx)) :
    Function.Bijective (HomotopyGroup.piMap (n + 1) q ha) := by
  subst y
  subst b
  exact piMap_target_bijective_of_fiberMap p q sq x a h n hfhi hphi hflo hplo

end Topology.HomotopyFiber
