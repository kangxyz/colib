/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.EtaleCohomology.ProperStrictlyHenselianRestriction
public import Colib.AlgebraicGeometry.Modules.Invertible.PicardRoot
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Picard.RootsOfUnitySecondCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Picard.MultiplicativeFirstCohomologyNaturality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootsOfUnityModule

/-!
# Kummer classes and proper specialization of Picard divisibility

The Kummer boundary of a Picard class has kernel exactly `n Pic(X)`. Hence it induces
an injection of `Pic(X)/n` into `H²(X, μ_n)`, without any vanishing hypothesis on
`H²(X, Gm)`. Naturality uses the native pullback on invertible modules and the native
inverse-image comparison on roots of unity. Proper base change over a strictly henselian
local ring then reflects divisibility of Picard classes from the closed fibre.

The general boundary and its naturality allow independent coefficient and Ext universes.
The proper specialization uses coefficient and Ext universe `u + 1`, as in COL-1030.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.EtaleCohomology

universe w v u

namespace Stacks.Kummer

section General

variable (X : Scheme.{u}) {n : ℕ} (hn0 : n ≠ 0)
  (hX : IsUnit ((n : ℕ) : Γ(X, ⊤)))
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- The Kummer class of a line bundle class, via the canonical identification of Picard
classes with first cohomology of the multiplicative sheaf. -/
def picardKummerClass :
    Picard.ofScheme X →+ Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} X n) 2 :=
  (kummerδ.{w, u, v} X hn0 hX 1).comp
    (etaleH1MultiplicativeAddEquivPicard.{w, v, u} X).symm.toAddMonoidHom

/-- A Picard class has zero Kummer class precisely when it is an `n`-fold multiple. -/
theorem picardKummerClass_eq_zero_iff (L : Picard.ofScheme X) :
    picardKummerClass.{w, v, u} X hn0 hX L = 0 ↔ ∃ M, n • M = L := by
  let e := etaleH1MultiplicativeAddEquivPicard.{w, v, u} X
  change kummerδ X hn0 hX 1 (e.symm L) = 0 ↔ _
  rw [← AddMonoidHom.mem_ker, ker_kummerδ_one]
  change (∃ y, n • y = e.symm L) ↔ _
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨e y, (map_nsmul e n y).symm.trans
      ((congrArg e hy).trans (e.apply_symm_apply L))⟩
  · rintro ⟨M, hM⟩
    exact ⟨e.symm M, (map_nsmul e.symm n M).symm.trans (congrArg e.symm hM)⟩

/-- The kernel of the Picard Kummer boundary is `n Pic(X)`. -/
theorem ker_picardKummerClass :
    (picardKummerClass.{w, v, u} X hn0 hX).ker =
      (nsmulAddMonoidHom n : Picard.ofScheme X →+ Picard.ofScheme X).range := by
  ext L
  simpa only [AddMonoidHom.mem_ker, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
    using picardKummerClass_eq_zero_iff.{w, v, u} X hn0 hX L

/-- The canonical Kummer map out of `Pic(X)/n Pic(X)`. -/
def picardQuotientKummerMap :
    Picard.ofScheme X ⧸ (nsmulAddMonoidHom n : Picard.ofScheme X →+ Picard.ofScheme X).range →+
      Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} X n) 2 :=
  QuotientAddGroup.lift _ (picardKummerClass.{w, v, u} X hn0 hX)
    (ker_picardKummerClass.{w, v, u} X hn0 hX).symm.le

/-- Kummer gives an injection, without assuming vanishing of the Brauer cohomology group. -/
theorem injective_picardQuotientKummerMap :
    Function.Injective (picardQuotientKummerMap.{w, v, u} X hn0 hX) :=
  (QuotientAddGroup.injective_lift_iff _ _ _).2
    (ker_picardKummerClass.{w, v, u} X hn0 hX).symm

/-- On representatives the quotient Kummer map is the Picard Kummer boundary. -/
@[simp]
theorem picardQuotientKummerMap_mk (L : Picard.ofScheme X) :
    picardQuotientKummerMap.{w, v, u} X hn0 hX (QuotientAddGroup.mk L) =
      picardKummerClass.{w, v, u} X hn0 hX L := rfl

end General

/-- The Picard Kummer boundary commutes with the actual pullback of invertible modules. -/
theorem picardKummerClass_naturality {X Y : Scheme.{u}} (π : X ⟶ Y) {n : ℕ}
    (hn0 : n ≠ 0) (hY : IsUnit ((n : ℕ) : Γ(Y, ⊤)))
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (L : Picard.ofScheme Y) :
    rootsOfUnityPullbackMap.{u, v, w} π n 2 (picardKummerClass.{w, v, u} Y hn0 hY L) =
      picardKummerClass.{w, v, u} X hn0 (isUnit_natCast_of_hom π hY)
        (Picard.schemePullbackClassHom π L) := by
  let x := (etaleH1MultiplicativeAddEquivPicard.{w, v, u} Y).symm L
  have hx : Sheaf.H.map (multiplicativeInverseImageComparison.{u, v} π) 1
      (etaleCohomologyRestrictionMap.{u, v, w} π _ 1 x) =
      (etaleH1MultiplicativeAddEquivPicard.{w, v, u} X).symm
        (Picard.schemePullbackClassHom π L) := by
    apply (etaleH1MultiplicativeAddEquivPicard.{w, v, u} X).injective
    simpa [x] using etaleH1MultiplicativeAddEquivPicard_naturality.{w, v, u} π x
  have h := etaleCohomologyRestrictionMap_kummerExtClass.{u, v, w}
    π hn0 hY 1 2 rfl x
  rw [hx] at h
  exact h

section Proper

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] hasExt_sheaf_smallEtale_succ

variable (R : Type u) [CommRing R] [StrictlyHenselianLocalRing R]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]
  {n : ℕ} (hn0 : n ≠ 0) (hX : IsUnit ((n : ℕ) : Γ(X, ⊤)))

include hn0 hX

/-- Proper closed-fibre restriction remains bijective after the canonical roots-of-unity
coefficient comparison. -/
theorem bijective_rootsOfUnityPullbackMap_closedFibre :
    Function.Bijective
      (rootsOfUnityPullbackMap.{u, 0, u + 1} (closedFibreInclusion R f) n 2) := by
  have hcomp := isIso_rootsOfUnityInverseImageComparison.{u, 0}
    (closedFibreInclusion R f) n hX
  have hb : Function.Bijective
      (Sheaf.H.map (rootsOfUnityInverseImageComparison.{u, 0}
        (closedFibreInclusion R f) n) 2) :=
    Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso _ 2
  apply hb.comp
    (bijective_etaleCohomologyRestrictionMap_closedFibre_of_strictlyHenselian R f
      (n := n) (Nat.pos_of_ne_zero hn0) 2 (rootsOfUnitySheaf.{u, 0} X n) ?_)
  simpa only [natCast_zsmul] using nsmul_id_rootsOfUnitySheaf_univ.{u, 0} X n

/-- For a proper scheme over a strictly henselian local ring, a Picard class is divisible
by an invertible positive integer if and only if its restriction to the closed fibre is.
No vanishing of second cohomology of the multiplicative sheaf is required. -/
@[colib_tag "COL-1031", stacks 03PL
  "Kummer exactness and proper base change reflect divisibility of Picard classes \
  from the closed fibre",
  colib_ref "axiom_stacks_5ed82d14"
    "AlgebraicGeometry/EtaleCohomology/KummerTheory/InverseImage.lean:866-894"
    "ingredient" "Naturality of the Kummer boundary with the canonical \
    inverse-image coefficient comparison"]
theorem picard_nsmul_exists_iff_closedFibre (L : Picard.ofScheme X) :
    (∃ M, n • M = L) ↔
      ∃ M, n • M = Picard.schemePullbackClassHom (closedFibreInclusion R f) L := by
  constructor
  · rintro ⟨M, rfl⟩
    exact ⟨Picard.schemePullbackClassHom (closedFibreInclusion R f) M,
      (map_nsmul (Picard.schemePullbackClassHom (closedFibreInclusion R f)) n M).symm⟩
  · intro h
    apply (picardKummerClass_eq_zero_iff.{u + 1, 0, u} X hn0 hX L).1
    apply (bijective_rootsOfUnityPullbackMap_closedFibre R f hn0 hX).injective
    rw [map_zero, picardKummerClass_naturality]
    exact (picardKummerClass_eq_zero_iff.{u + 1, 0, u} _ hn0 _ _).2 h

/-- An actual tensor root of the closed-fibre pullback implies existence of an actual
global tensor root. This does not assert that the particular fibre root or its chosen
isomorphism extends. -/
@[colib_tag "COL-1031"]
theorem exists_schemeTensorPower_iso_of_closedFibre
    (L : X.Modules) (hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L)
    (M₀ : (closedFibre R f).Modules)
    (hM₀ : Stacks.SheafOfModules.IsInvertible (closedFibre R f).presheaf
      (closedFibre R f).ringCatIsSheaf M₀)
    (e₀ : Stacks.SheafOfModules.schemeTensorPower (closedFibre R f) M₀ hM₀ (n : ℤ) ≅
      (Scheme.Modules.pullback (closedFibreInclusion R f)).obj L) :
    ∃ (M : X.Modules) (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M),
      Nonempty (Stacks.SheafOfModules.schemeTensorPower X M hM (n : ℤ) ≅ L) := by
  apply exists_schemeTensorPower_iso_of_picard_nsmul X n L hL
  apply (picard_nsmul_exists_iff_closedFibre R f hn0 hX (X.picardClass L hL)).2
  refine ⟨(closedFibre R f).picardClass M₀ hM₀, ?_⟩
  exact nsmul_picardClass_eq_pullback_of_schemeTensorPower_iso
    (closedFibreInclusion R f) n L hL M₀ hM₀ e₀

end Proper

end Stacks.Kummer
