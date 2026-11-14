/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Hom.Instances

/-! # Exact group ladders and the original Mayer–Vietoris difference

The three diagram chases retain the original maps and the first-minus-second
difference. The global-term result includes degree zero; the positive local-pair result uses an
actual upper boundary. The final
criterion instead uses reflection of the original image.

Source: `Quillen/Aglib/Algebra/Group/MayerVietoris.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section

namespace GroupMayerVietoris
universe u v w x y z
variable {A : Type u} {B : Type v} {C : Type w} {D : Type x} {E : Type y} {S : Type z}
  [Group A] [Group B] [Group C] [Group D] [CommGroup E] [Group S]

/-- The two original restriction maps, in first-then-second order. -/
def pair (f : B →* C) (g : B →* D) : B →* C × D := f.prod g

/-- The actual difference is first restriction times inverse second restriction. -/
def difference (u : C →* E) (v : D →* E) : C × D →* E where
  toFun x := u x.1 * (v x.2)⁻¹
  map_one' := by simp
  map_mul' a b := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_inv_rev]
    ac_rfl

@[simp] lemma difference_apply (u : C →* E) (v : D →* E) (c : C) (d : D) :
    difference u v (c,d) = u c * (v d)⁻¹ := rfl

lemma mem_difference_ker (u : C →* E) (v : D →* E) (x : C × D) :
    x ∈ (difference u v).ker ↔ u x.1 = v x.2 := by
  change u x.1 * (v x.2)⁻¹ = 1 ↔ _
  exact mul_inv_eq_one

/-- Exactness at the global term only uses exactness at the two support terms.
It therefore applies in degree zero without a surjectivity assumption. -/
lemma range_boundary_eq_ker_pair (h : A →* B) (q : E →* A)
    (f : B →* C) (g : B →* D)
    (hh : h.range = f.ker) (hq : q.range = (g.comp h).ker) :
    (h.comp q).range = (pair f g).ker := by
  ext b
  constructor
  · rintro ⟨e,rfl⟩
    have hx : h (q e) ∈ f.ker := hh ▸ (show h (q e) ∈ h.range from ⟨q e,rfl⟩)
    have hy : q e ∈ (g.comp h).ker := hq ▸ (show q e ∈ q.range from ⟨e,rfl⟩)
    change (f (h (q e)), g (h (q e))) = (1,1)
    exact Prod.ext hx hy
  · intro hb
    have hb' : f b = 1 ∧ g b = 1 := by
      change (f b, g b) = (1,1) at hb
      exact ⟨congrArg Prod.fst hb,congrArg Prod.snd hb⟩
    have hm : b ∈ h.range := hh.symm ▸ (show b ∈ f.ker from hb'.1)
    obtain ⟨a,ha⟩ := hm
    have hn : a ∈ q.range := hq.symm ▸ (show a ∈ (g.comp h).ker by
      change g (h a) = 1
      rw [ha]
      exact hb'.2)
    obtain ⟨e,he⟩ := hn
    exact ⟨e, by change h (q e) = b; rw [he,ha]⟩

/-- Exactness at the overlap term, with the indicated difference sign. -/
lemma range_difference_eq_ker_boundary (h : A →* B) (p : C →* A) (q : E →* A)
    (u : C →* E) (v : D →* E)
    (hp : p.range = h.ker) (hv : v.range = q.ker)
    (hqu : q.comp u = p) :
    (difference u v).range = (h.comp q).ker := by
  have hqu' (c : C) : q (u c) = p c := DFunLike.congr_fun hqu c
  have hhp (c : C) : h (p c) = 1 := by
    change p c ∈ h.ker
    rw [← hp]
    exact ⟨c,rfl⟩
  have hqv (d : D) : q (v d) = 1 := by
    change v d ∈ q.ker
    rw [← hv]
    exact ⟨d,rfl⟩
  ext e
  constructor
  · rintro ⟨⟨c,d⟩,rfl⟩
    change h (q (u c * (v d)⁻¹)) = 1
    rw [map_mul, map_inv, hqu', hqv, inv_one, mul_one, hhp]
  · intro he
    have hm : q e ∈ p.range := hp.symm ▸ (show q e ∈ h.ker from he)
    obtain ⟨c,hc⟩ := hm
    have hn : (u c)⁻¹ * e ∈ v.range := hv.symm ▸
      (show (u c)⁻¹ * e ∈ q.ker by
        change q ((u c)⁻¹ * e) = 1
        rw [map_mul, map_inv, hqu', hc, inv_mul_cancel])
    obtain ⟨d,hd⟩ := hn
    refine ⟨(c,d⁻¹),?_⟩
    change u c * (v (d⁻¹))⁻¹ = e
    rw [map_inv, inv_inv, hd, mul_inv_cancel_left]

/-- Exactness at the pair of positive local terms. The upper boundary is an
actual map at this stage; the statement does not fabricate one in degree zero. -/
lemma range_pair_eq_ker_difference (h : A →* B) (f : B →* C) (g : B →* D)
    (u : C →* E) (v : D →* E) (p : C →* S) (q : E →* S)
    (hh : h.range = f.ker) (hg : (g.comp h).range = v.ker)
    (hf : f.range = p.ker) (hv : v.range = q.ker)
    (hcomm : u.comp f = v.comp g) (hqu : q.comp u = p) :
    (pair f g).range = (difference u v).ker := by
  have hcomm' (b : B) : u (f b) = v (g b) := DFunLike.congr_fun hcomm b
  have hqu' (c : C) : q (u c) = p c := DFunLike.congr_fun hqu c
  have hqv (d : D) : q (v d) = 1 := by
    change v d ∈ q.ker
    rw [← hv]
    exact ⟨d,rfl⟩
  have hfh (a : A) : f (h a) = 1 := by
    change h a ∈ f.ker
    rw [← hh]
    exact ⟨a,rfl⟩
  ext x
  rw [mem_difference_ker]
  constructor
  · rintro ⟨b,rfl⟩
    exact hcomm' b
  · intro hx
    have hc : x.1 ∈ f.range := hf.symm ▸ (show x.1 ∈ p.ker by
      change p x.1 = 1
      rw [← hqu', hx, hqv])
    obtain ⟨b,hb⟩ := hc
    have hd : x.2 * (g b)⁻¹ ∈ (g.comp h).range := hg.symm ▸
      (show x.2 * (g b)⁻¹ ∈ v.ker by
        change v (x.2 * (g b)⁻¹) = 1
        rw [map_mul, map_inv, ← hcomm', hb, hx, mul_inv_cancel])
    obtain ⟨a,ha⟩ := hd
    refine ⟨h a * b, ?_⟩
    apply Prod.ext
    · change f (h a * b) = x.1
      rw [map_mul, hfh, one_mul, hb]
    · change g (h a * b) = x.2
      rw [map_mul]
      change g (h a) = x.2 * (g b)⁻¹ at ha
      rw [ha, inv_mul_cancel_right]

end GroupMayerVietoris

/-! # The precise extra image-reflection criterion for final local-pair exactness -/
namespace GroupMayerVietoris
universe u v w x y
variable {A : Type u} {B : Type v} {C : Type w} {D : Type x} {E : Type y}
  [Group A] [Group B] [Group C] [Group D] [CommGroup E]

/-- Actual image reflection supplies the final pair position without inventing
a negative connecting homomorphism. -/
lemma range_pair_eq_ker_difference_of_image_reflection (h : A →* B) (f : B →* C) (g : B →* D)
    (u : C →* E) (v : D →* E)
    (hh : h.range = f.ker) (hg : (g.comp h).range = v.ker)
    (hcomm : u.comp f = v.comp g)
    (hreflect : ∀ c, u c ∈ v.range → c ∈ f.range) :
    (pair f g).range = (difference u v).ker := by
  have hcomm' (b : B) : u (f b) = v (g b) := DFunLike.congr_fun hcomm b
  have hfh (a : A) : f (h a) = 1 := by
    change h a ∈ f.ker
    rw [← hh]
    exact ⟨a,rfl⟩
  ext x
  rw [mem_difference_ker]
  constructor
  · rintro ⟨b,rfl⟩
    exact hcomm' b
  · intro hx
    have hc : x.1 ∈ f.range := hreflect x.1 ⟨x.2,hx.symm⟩
    obtain ⟨b,hb⟩ := hc
    have hd : x.2 * (g b)⁻¹ ∈ (g.comp h).range := hg.symm ▸
      (show x.2 * (g b)⁻¹ ∈ v.ker by
        change v (x.2 * (g b)⁻¹) = 1
        rw [map_mul, map_inv, ← hcomm', hb, hx, mul_inv_cancel])
    obtain ⟨a,ha⟩ := hd
    refine ⟨h a * b, ?_⟩
    apply Prod.ext
    · change f (h a * b) = x.1
      rw [map_mul, hfh, one_mul, hb]
    · change g (h a * b) = x.2
      rw [map_mul]
      change g (h a) = x.2 * (g b)⁻¹ at ha
      rw [ha, inv_mul_cancel_right]

end GroupMayerVietoris
