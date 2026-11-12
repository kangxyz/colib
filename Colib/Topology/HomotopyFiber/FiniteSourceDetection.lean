/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References
public import Colib.Topology.HomotopyFiber.FiniteTargetDetection

/-! # Finite source detection from the original fiber ladder

The original source in degree n+2 is detected using precisely the surrounding
positive degrees of the target and actual fiber map. All specified points are retained.
-/
/-! Implementation provenance:
`Quillen/Topology/HomotopyFiber/FiniteSourceDetection.lean` at Quillen commit
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

/-- Four exact neighboring maps detect the source in degree n+2. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyFiber/FiniteSourceDetection.lean:28"
  "adaptation" "Original finite-range ladder and stable proper-row roof."]
theorem piMap_source_bijective_of_fiberMap (n : ℕ)
    (hqhi : Function.Surjective (HomotopyGroup.piMap (n + 2) q (x := a) rfl))
    (hfhi : Function.Bijective (HomotopyGroup.piMap (n + 1) (map p q sq a)
      (map_basepoint p q sq x a h)))
    (hqlo : Function.Bijective (HomotopyGroup.piMap (n + 1) q (x := a) rfl))
    (hflo : Function.Injective (HomotopyGroup.piMap n (map p q sq a)
      (map_basepoint p q sq x a h))) :
    Function.Bijective (HomotopyGroup.piMap (n + 1) p (x := x) rfl) := by
  let h' : g (p x) = q a :=
    (ContinuousMap.congr_fun sq x).symm.trans (congrArg q h)
  refine MonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (connectingHom f a x h (n + 1))
    (HomotopyGroup.piMap (n + 1) (projection f a) (projection_basepoint f a x h))
    (HomotopyGroup.piMap (n + 1) f h) (connectingHom f a x h n)
    (connectingHom g (q a) (p x) h' (n + 1))
    (HomotopyGroup.piMap (n + 1) (projection g (q a)) (projection_basepoint g (q a) (p x) h'))
    (HomotopyGroup.piMap (n + 1) g h') (connectingHom g (q a) (p x) h' n)
    (HomotopyGroup.piMap (n + 2) q rfl)
    (HomotopyGroup.piMap (n + 1) (map p q sq a) (map_basepoint p q sq x a h))
    (HomotopyGroup.piMap (n + 1) p rfl) (HomotopyGroup.piMap (n + 1) q rfl)
    (HomotopyGroup.piMap n (map p q sq a) (map_basepoint p q sq x a h))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hqhi hfhi hqlo hflo
  · exact (connectingHom_natural p q sq x a h (n + 1)).symm
  · exact (projectionHom_natural p q sq x a h (n + 1)).symm
  · exact (originalHom_natural p q sq x a h (n + 1)).symm
  · exact (connectingHom_natural p q sq x a h n).symm
  · exact MonoidHom.mulExact_iff.mpr (range_connectingHom_eq_ker_projection f a x h (n + 1)).symm
  · exact MonoidHom.mulExact_iff.mpr (piMap_range_projection_eq_ker f a x h (n + 1)).symm
  · exact MonoidHom.mulExact_iff.mpr (range_piMap_eq_ker_connectingHom f a x h n).symm
  · exact MonoidHom.mulExact_iff.mpr
      (range_connectingHom_eq_ker_projection g (q a) (p x) h' (n + 1)).symm
  · exact MonoidHom.mulExact_iff.mpr
      (piMap_range_projection_eq_ker g (q a) (p x) h' (n + 1)).symm
  · exact MonoidHom.mulExact_iff.mpr (range_piMap_eq_ker_connectingHom g (q a) (p x) h' n).symm

/-- The finite source ladder retains both displayed target points. -/
@[colib_ref "quillen" "Quillen/Topology/HomotopyFiber/FiniteSourceDetection.lean:64"
  "adaptation" "Original finite-range ladder and stable proper-row roof."]
theorem piMap_source_bijective_of_basedFiberMap (y : Y) (b : B)
    (h' : g y = b) (hx : p x = y) (ha : q a = b) (n : ℕ)
    (hqhi : Function.Surjective (HomotopyGroup.piMap (n + 2) q ha))
    (hfhi : Function.Bijective (HomotopyGroup.piMap (n + 1) (mapAt p q sq a b ha)
      (mapAt_basepoint p q sq x a y b h h' hx ha)))
    (hqlo : Function.Bijective (HomotopyGroup.piMap (n + 1) q ha))
    (hflo : Function.Injective (HomotopyGroup.piMap n (mapAt p q sq a b ha)
      (mapAt_basepoint p q sq x a y b h h' hx ha))) :
    Function.Bijective (HomotopyGroup.piMap (n + 1) p hx) := by
  subst y
  subst b
  exact piMap_source_bijective_of_fiberMap p q sq x a h n hqhi hfhi hqlo hflo

end Topology.HomotopyFiber
