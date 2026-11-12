/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.BasedHomotopySquareMap
public import Colib.Topology.HomotopyFiber.LESNaturality

/-!
# Original connecting maps for based homotopy squares

A homotopy-commuting square of continuous maps gives a map of their actual
path-space fibers. When the supplied square homotopy stays at the target
basepoint over the source basepoint, the original connecting homomorphisms
commute with this fiber map. Both the whole square track and the prescribed
endpoint equalities are retained.

`connectingHom_basedHomotopySquare_natural` supplies the endpoint-aware
statement. The loop-inclusion square is proved by an explicit based homotopy
that removes the constant initial path segment. No contractibility or
weak-equivalence assumptions on the spaces are required.
-/

/-! Implementation source: `Quillen/Topology/HomotopyFiber/BasedHomotopyConnecting.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`; actual maps, basepoints and tracks are retained. -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v u' v'

open HomotopyGroup
open scoped Topology unitInterval

namespace Topology.HomotopyFiber

variable {X : Type u} {Y : Type v} {X' : Type u'} {Y' : Type v'}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
  {f : C(X, Y)} {g : C(X', Y')}
  (u : C(X, X')) (v : C(Y, Y')) (H : (v.comp f).Homotopy (g.comp u))
  (x : X) (y : Y) (h : f x = y) (h' : g (u x) = v y)
  (hzero : ∀ t, H (t, x) = v y)

/-- Remove the constant square-track prefix in the actual loop-inclusion square. -/
def basedSquareLoopInclusionHomotopy :
    ((homotopySquareMap u v H y).comp (loopInclusion f y x h)).Homotopy
      ((loopInclusion g (v y) (u x) h').comp (basedLoopMap v rfl)) where
  toFun z := loopInclusion g (v y) (u x) h'
    (Path.delayReflLeft z.1 (basedLoopMap v rfl z.2))
  continuous_toFun := (loopInclusion g (v y) (u x) h').continuous.comp
    (Path.continuous_delayReflLeft.comp
      (continuous_fst.prodMk ((basedLoopMap v rfl).continuous.comp continuous_snd)))
  map_zero_left γ := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply ContinuousMap.ext
      intro t
      change Path.delayReflLeft 0 (basedLoopMap v rfl γ) t =
        ((H.evalAt x).symm.trans ((toPath f y (loopInclusion f y x h γ)).map v.continuous)) t
      rw [Path.delayReflLeft_zero, Path.trans_apply, Path.trans_apply]
      split_ifs
      · exact (hzero _).symm
      · rfl
  map_one_left γ := by
    change loopInclusion g (v y) (u x) h'
      (Path.delayReflLeft 1 (basedLoopMap v rfl γ)) = _
    rw [Path.delayReflLeft_one]
    rfl

/-- The whole loop-inclusion homotopy fixes the constant-loop basepoint. -/
theorem basedSquareLoopInclusionHomotopy_based (t : unitInterval) :
    basedSquareLoopInclusionHomotopy u v H x y h h' hzero (t, Path.refl y) =
      basepoint g (v y) (u x) h' := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply ContinuousMap.ext
    intro s
    rfl

include hzero in
/-- A square track fixed at zero preserves the actual constant-path fiber basepoint. -/
theorem homotopySquareMap_basepoint :
    homotopySquareMap u v H y (basepoint f y x h) = basepoint g (v y) (u x) h' :=
  ((basedSquareLoopInclusionHomotopy u v H x y h h' hzero).map_zero_left (Path.refl y)).symm.trans
    (basedSquareLoopInclusionHomotopy_based u v H x y h h' hzero 0)

/-- Original connecting naturality for the given whole based homotopy square. -/
theorem connectingHom_homotopySquare_natural (n : ℕ) :
    (piMap n (homotopySquareMap u v H y)
      (homotopySquareMap_basepoint u v H x y h h' hzero)).comp (connectingHom f y x h n) =
      (connectingHom g (v y) (u x) h' n).comp (piMap (n + 1) v rfl) := by
  have hloop :
      (piMap n (homotopySquareMap u v H y)
        (homotopySquareMap_basepoint u v H x y h h' hzero)).comp
          (piMap n (loopInclusion f y x h) (loopInclusion_refl f y x h)) =
      (piMap n (loopInclusion g (v y) (u x) h') (loopInclusion_refl g (v y) (u x) h')).comp
        (piMap n (basedLoopMap v rfl) (basedLoopMap_refl v rfl)) := by
    rw [← HomotopyGroup.mapHom_comp, ← HomotopyGroup.mapHom_comp]
    exact piMap_eq_of_based_homotopy n _ _
      (basedSquareLoopInclusionHomotopy u v H x y h h' hzero)
      (basedSquareLoopInclusionHomotopy_based u v H x y h h' hzero)
  unfold connectingHom
  rw [← MonoidHom.comp_assoc, hloop, MonoidHom.comp_assoc,
    loopShiftMulEquiv_natural, ← MonoidHom.comp_assoc]

/-- The actual homotopy-square map retains the specified target fiber basepoint. -/
theorem basedHomotopySquareMap_basepoint
    (x' : X') (y' : Y') (hx : u x = x') (hy : v y = y') (hg : g x' = y')
    (Hbase : ∀ t, H (t, x) = y') :
    basedHomotopySquareMap u v H y y' hy (basepoint f y x h) =
      basepoint g y' x' hg := by
  subst x'
  subst y'
  exact homotopySquareMap_basepoint u v H x y h hg Hbase

/-- Endpoint-aware original connecting naturality for a genuine based homotopy
square, retaining the complete supplied square track in the actual fiber map. -/
theorem connectingHom_basedHomotopySquare_natural
    (x' : X') (y' : Y') (hx : u x = x') (hy : v y = y') (hg : g x' = y')
    (Hbase : ∀ t, H (t, x) = y') (n : ℕ) :
    (piMap n (basedHomotopySquareMap u v H y y' hy)
      (basedHomotopySquareMap_basepoint u v H x y h x' y' hx hy hg Hbase)).comp
        (connectingHom f y x h n) =
      (connectingHom g y' x' hg n).comp (piMap (n + 1) v hy) := by
  subst x'
  subst y'
  exact connectingHom_homotopySquare_natural u v H x y h hg Hbase n

end Topology.HomotopyFiber
