/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.GraphExterior.Prime
public import Colib.AlgebraicGeometry.Correspondences.Exterior.Additive

/-!
# Power-cut normalization on signed exterior identity correspondences

Both cuts are admissible on every exterior identity prime for a positive
exponent. Extend the prime comparison by the existing integer coefficients
of native finite correspondences. This gives the diagonal identity part of
Voevodsky's Lemma 4.3.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Stacks.Chow
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Cor

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Gₖ" => SmoothSite.multiplicativeGroupObject Sₖ

variable (X Y : SmoothSite (Spec (CommRingCat.of k)))

local notation "XG" => SmoothSite.product X Gₖ
local notation "YG" => SmoothSite.product Y Gₖ

/-- The original signed exterior identity with its power-cut domain witness. -/
def nativeExteriorToTorusPowerCutDomain (n : ℕ) (hn : n ≠ 0) :
    (Cor.mk X ⟶ Cor.mk Y) →+ torusPowerCutDomain k X Y n :=
  liftFiniteCorrespondence X.hom Y.hom fun z hz =>
    ⟨singleFiniteCorrespondence (XG).hom (YG).hom
      (nativeExteriorPoint X Y Gₖ z hz) (nativeExteriorPoint_admissible X Y Gₖ z hz) 1,
      single_mem_torusPowerCutDomain k X Y (nativeExteriorPoint X Y Gₖ z hz) n
        (nativeExteriorPoint_admissible X Y Gₖ z hz)
        (nativeExteriorPoint_torusPowerCutAdmissibleAt k X Y z hz n hn) 1⟩

/-- Forgetting the domain witness gives the existing signed exterior operation. -/
theorem nativeExteriorToTorusPowerCutDomain_val (n : ℕ) (hn : n ≠ 0)
    (c : Cor.mk X ⟶ Cor.mk Y) :
    (nativeExteriorToTorusPowerCutDomain k X Y n hn c).val = nativeExterior X Y Gₖ c := by
  have h : (torusPowerCutDomain k X Y n).subtype.comp
      (nativeExteriorToTorusPowerCutDomain k X Y n hn) = nativeExterior X Y Gₖ := by
    apply finiteCorrespondences.addHom_ext_one X.hom Y.hom
    intro z hz
    simp only [AddMonoidHom.comp_apply, nativeExteriorToTorusPowerCutDomain,
      liftFiniteCorrespondence_single, one_zsmul]
    change singleFiniteCorrespondence (XG).hom (YG).hom (nativeExteriorPoint X Y Gₖ z hz)
      (nativeExteriorPoint_admissible X Y Gₖ z hz) 1 =
        nativeExterior X Y Gₖ (singleFiniteCorrespondence X.hom Y.hom z hz 1)
    calc
      _ = nativeExteriorPrime X Y Gₖ z hz := (nativeExteriorPrime_eq_single X Y Gₖ z hz).symm
      _ = _ := by rw [nativeExterior_single, one_zsmul]
  exact DFunLike.congr_fun h c

/-- Applying the native signed power cut to the exterior identity returns the original
correspondence, with every signed prime coefficient. -/
theorem torusPowerCut_nativeExteriorToTorusPowerCutDomain (n : ℕ) (hn : n ≠ 0)
    (c : Cor.mk X ⟶ Cor.mk Y) :
    torusPowerCut k X Y n (nativeExteriorToTorusPowerCutDomain k X Y n hn c) = c := by
  have h : (torusPowerCut k X Y n).comp (nativeExteriorToTorusPowerCutDomain k X Y n hn) =
      AddMonoidHom.id (Cor.mk X ⟶ Cor.mk Y) := by
    apply finiteCorrespondences.addHom_ext_one X.hom Y.hom
    intro z hz
    simp only [AddMonoidHom.comp_apply, nativeExteriorToTorusPowerCutDomain,
      liftFiniteCorrespondence_single, one_zsmul]
    let zG := nativeExteriorPoint X Y Gₖ z hz
    let hzG := nativeExteriorPoint_admissible X Y Gₖ z hz
    let hc := nativeExteriorPoint_torusPowerCutAdmissibleAt k X Y z hz n hn
    change torusPowerCut k X Y n ⟨singleFiniteCorrespondence (XG).hom (YG).hom zG hzG 1,
      single_mem_torusPowerCutDomain k X Y zG n hzG hc 1⟩ =
        singleFiniteCorrespondence X.hom Y.hom z hz 1
    calc
      _ = (1 : ℤ) • torusPowerCutPrime k X Y zG n hc := torusPowerCut_single k X Y zG n hzG hc 1
      _ = _ := by
        rw [one_zsmul]
        exact torusPowerCutPrime_nativeExteriorPoint k X Y z hz n hn hc
  exact DFunLike.congr_fun h c

end AlgebraicGeometry.Cor
