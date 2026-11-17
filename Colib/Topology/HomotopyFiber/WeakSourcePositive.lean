/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.GroupDetection

/-! # Weak source changes on positive homotopy groups of the actual fibers

The original source-change fiber map retains the base path. A direct five-term
LES argument uses the original total-space maps in the two adjacent degrees.
The separate zeroth homotopy-set assertion is not assumed or claimed here.

## Implementation provenance

Adapted from `Quillen/Topology/HomotopyFiber/WeakSourcePositive.lean` at Quillen
commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
namespace Topology.HomotopyFiber

variable {X : Type u} {Y : Type v} {B : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace B]
  (f : C(X, B)) (g : C(Y, B)) (u : C(X, Y)) (sq : g.comp u = f)
  (x : X) (b : B) (hx : f x = b)

/-- Bijectivity on the original total homotopy groups in degree `n + 1` and surjectivity
in degree `n + 2` give bijectivity on the original fiber group in degree `n + 1`. -/
theorem piMap_mapOver_bijective (n : ℕ)
    (hcurrent : Function.Bijective (HomotopyGroup.piMap n u (x := x) rfl))
    (hnext : Function.Surjective (HomotopyGroup.piMap (n + 1) u (x := x) rfl)) :
    Function.Bijective (HomotopyGroup.piMap n (mapOver f g u sq b)
      (mapOver_basepoint f g u sq x b hx)) := by
  let hy := (ContinuousMap.congr_fun sq x).trans hx
  let v := HomotopyGroup.piMap n (mapOver f g u sq b) (mapOver_basepoint f g u sq x b hx)
  let i₁ := HomotopyGroup.piMap n (projection f b) (projection_basepoint f b x hx)
  let i₂ := HomotopyGroup.piMap n (projection g b) (projection_basepoint g b (u x) hy)
  let p₁ := HomotopyGroup.piMap n f hx
  let p₂ := HomotopyGroup.piMap n g hy
  let m := HomotopyGroup.piMap n u (x := x) rfl
  have wi (a) : m (i₁ a) = i₂ (v a) :=
    homotopyGroupMap_projection_natural u (ContinuousMap.id B) sq.symm x b hx a
  have wp (a) : p₂ (m a) = p₁ a := by
    change HomotopyGroup.map g hy (HomotopyGroup.map u rfl a) = HomotopyGroup.map f hx a
    have h := homotopyGroupMap_square_natural u (ContinuousMap.id B) sq.symm x b hx a
    rw [HomotopyGroup.map_id] at h
    exact h.symm
  have wd (a) : v (connectingHom f b x hx n a) = connectingHom g b (u x) hy n a := by
    change HomotopyGroup.map (map u (ContinuousMap.id B) sq.symm b) _
      (connectingMap f b x hx (n + 1) a) = connectingMap g b (u x) hy (n + 1) a
    have h := connectingMap_natural u (ContinuousMap.id B) sq.symm x b hx (n + 1) a
    rw [HomotopyGroup.map_id] at h
    exact h
  have wp_next (a : HomotopyGroup.Pi (n + 2) X x) :
      HomotopyGroup.piMap (n + 1) f hx a =
        HomotopyGroup.piMap (n + 1) g hy (HomotopyGroup.piMap (n + 1) u rfl a) := by
    change HomotopyGroup.map f hx a = HomotopyGroup.map g hy (HomotopyGroup.map u rfl a)
    have h := homotopyGroupMap_square_natural u (ContinuousMap.id B) sq.symm x b hx a
    rw [HomotopyGroup.map_id] at h
    exact h
  constructor
  · apply (injective_iff_map_eq_one v).2
    intro a ha
    have hi : i₁ a = 1 := hcurrent.injective (by rw [wi, ha, map_one, map_one])
    have hmem : a ∈ (connectingHom f b x hx n).range := by
      rw [range_connectingHom_eq_ker_projection]
      exact hi
    obtain ⟨d, hd⟩ := hmem
    have hδ : connectingHom g b (u x) hy n d = 1 := by rw [← wd, hd]; exact ha
    have hp : d ∈ (HomotopyGroup.piMap (n + 1) g hy).range := by
      rw [range_piMap_eq_ker_connectingHom]
      exact hδ
    obtain ⟨y, hy'⟩ := hp
    obtain ⟨z, hz⟩ := hnext y
    have hz' : HomotopyGroup.piMap (n + 1) f hx z = d :=
      (wp_next z).trans ((congrArg (HomotopyGroup.piMap (n + 1) g hy) hz).trans hy')
    have hδ' : connectingHom f b x hx n d = 1 := by
      have hmem : d ∈ (HomotopyGroup.piMap (n + 1) f hx).range := ⟨z, hz'⟩
      rw [range_piMap_eq_ker_connectingHom] at hmem
      exact hmem
    rw [hd] at hδ'
    exact hδ'
  · intro a
    obtain ⟨c, hc⟩ := hcurrent.surjective (i₂ a)
    have hp : p₁ c = 1 := by
      rw [← wp, hc]
      exact DFunLike.congr_fun (homotopyGroupMapHom_projection_comp g b (u x) hy) a
    obtain ⟨d, hd⟩ := (mem_range_projection_iff f b x hx c).2 hp
    have hi : i₂ (a * (v d)⁻¹) = 1 := by
      rw [map_mul, map_inv, ← wi, hd, hc, mul_inv_cancel]
    have hm : a * (v d)⁻¹ ∈ (connectingHom g b (u x) hy n).range := by
      rw [range_connectingHom_eq_ker_projection]
      exact hi
    obtain ⟨e, he⟩ := hm
    refine ⟨connectingHom f b x hx n e * d, ?_⟩
    change v (connectingHom f b x hx n e * d) = a
    rw [map_mul, wd, he, inv_mul_cancel_right]

end Topology.HomotopyFiber
