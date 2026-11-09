/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Intersection.FlatSectionStalkTor
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.TestModuleStalk
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Actual inverse-image support stalks along an open section

For `i : C ⟶ T` and `p : T ⟶ X` with `i ≫ p` open, the stalk of the actual
inverse-image closed subscheme of an ideal `I` on `X` is scalar extension of the
stalk of its actual restriction to `C`. The extension is the already constructed
`openSectionStalkExtension`, not an assumed comparison. Both source actions are
literal inclusion stalk maps, with all specified point equalities retained.

The proof uses the native ideal-stalk comap formula, native closed-subscheme
stalk quotient equivalence, and Mathlib's quotient/tensor equivalence. Nilpotents
are preserved. Flatness of `p` is needed only for positive Tor vanishing, not for
the stalk comparison or degree-zero isomorphism.

Source: `motivic_source_a6805c4`, `Composition/Identity/Tor.lean`,
`isZero_incidenceTor_succ_componentIdentity_right`, through its actual inverse-image
support calculation. References: Stacks, Tags 01PB and 0098; Mathlib,
`Algebra.TensorProduct.quotIdealMapEquivTensorQuot`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.IdealSheafData

/-- The native quotient/stalk equivalence with an explicitly specified ambient point.
The native ring equivalence is linear for the literal restricted action:
on quotient generators both scalar actions are multiplication by the inclusion
stalk map. No equality of opaque module instances is assumed. -/
def subschemeStalkModuleIsoQuotientOfEq {X : Scheme.{u}} (I : X.IdealSheafData)
    (x : X) (z : I.subscheme) (hz : x = I.subschemeι z) :
    (ModuleCat.restrictScalars
      ((X.presheaf.stalkCongr (.of_eq hz)).hom ≫ I.subschemeι.stalkMap z).hom).obj
      (ModuleCat.of (I.subscheme.presheaf.stalk z) (I.subscheme.presheaf.stalk z)) ≅
    ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x ⧸ stalk I x) := by
  subst x
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp]
  let M := (ModuleCat.restrictScalars (I.subschemeι.stalkMap z).hom).obj
    (ModuleCat.of (I.subscheme.presheaf.stalk z) (I.subscheme.presheaf.stalk z))
  let e : (X.presheaf.stalk (I.subschemeι z) ⧸ stalk I (I.subschemeι z))
      ≃ₗ[X.presheaf.stalk (I.subschemeι z)] M :=
    { toAddEquiv := (subschemeStalkQuotEquiv I z).toAddEquiv
      map_smul' := by
        intro r m
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective m
        change subschemeStalkQuotEquiv I z
          (Ideal.Quotient.mk (stalk I (I.subschemeι z)) (r * a)) =
            (I.subschemeι.stalkMap z).hom r * subschemeStalkQuotEquiv I z
              (Ideal.Quotient.mk (stalk I (I.subschemeι z)) a)
        rw [subschemeStalkQuotEquiv_mk, subschemeStalkQuotEquiv_mk]
        exact map_mul (I.subschemeι.stalkMap z).hom r a }
  exact e.symm.toModuleIso

end AlgebraicGeometry.IdealSheafData

namespace AlgebraicGeometry.Scheme.Hom

variable {C T X : Scheme.{u}} (i : C ⟶ T) (p : T ⟶ X)
  [IsOpenImmersion (i ≫ p)] (I : X.IdealSheafData) (c : C)

/-- The extended ideal is the actual inverse-image ideal at the actual ambient point. -/
theorem map_stalk_comap_openSection :
    Ideal.map (openSectionStalkExtension i p c)
      (IdealSheafData.stalk (I.comap (i ≫ p)) c) =
    IdealSheafData.stalk (I.comap p) (i c) := by
  rw [IdealSheafData.stalk_comap, IdealSheafData.stalk_comap, Ideal.map_map]
  congr 1
  change (((i ≫ p).stalkMap c) ≫
    inv ((i ≫ p).stalkMap c) ≫ p.stalkMap (i c)).hom = (p.stalkMap (i c)).hom
  simp

/-- The actual other pulled-support stalk is extension of the actual restricted-support stalk.
The inputs are actual points of the two native ideal subschemes, not quotient models. -/
def comapStalkIsoExtendOpenSection
    (d : (I.comap p).subscheme) (j : (I.comap (i ≫ p)).subscheme)
    (hd : i c = (I.comap p).subschemeι d)
    (hj : c = (I.comap (i ≫ p)).subschemeι j) :
    (ModuleCat.restrictScalars
      ((T.presheaf.stalkCongr (.of_eq hd)).hom ≫
        (I.comap p).subschemeι.stalkMap d).hom).obj
      (ModuleCat.of ((I.comap p).subscheme.presheaf.stalk d)
        ((I.comap p).subscheme.presheaf.stalk d)) ≅
    (ModuleCat.extendScalars (openSectionStalkExtension i p c)).obj
      ((ModuleCat.restrictScalars
        ((C.presheaf.stalkCongr (.of_eq hj)).hom ≫
          (I.comap (i ≫ p)).subschemeι.stalkMap j).hom).obj
        (ModuleCat.of ((I.comap (i ≫ p)).subscheme.presheaf.stalk j)
          ((I.comap (i ≫ p)).subscheme.presheaf.stalk j))) := by
  let a := openSectionStalkExtension i p c
  let : Algebra (C.presheaf.stalk c) (T.presheaf.stalk (i c)) := a.toAlgebra
  let J := IdealSheafData.stalk (I.comap (i ≫ p)) c
  let D := IdealSheafData.stalk (I.comap p) (i c)
  let eD := IdealSheafData.subschemeStalkModuleIsoQuotientOfEq (I.comap p) (i c) d hd
  let eJ := IdealSheafData.subschemeStalkModuleIsoQuotientOfEq (I.comap (i ≫ p)) c j hj
  let eQ : ModuleCat.of (T.presheaf.stalk (i c)) (T.presheaf.stalk (i c) ⧸ D) ≅
      (ModuleCat.extendScalars a).obj
        (ModuleCat.of (C.presheaf.stalk c) (C.presheaf.stalk c ⧸ J)) :=
    (Submodule.quotEquivOfEq _ _ (map_stalk_comap_openSection i p I c).symm).toModuleIso ≪≫
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot
        (T.presheaf.stalk (i c)) J).toLinearEquiv.toModuleIso
  exact eD ≪≫ eQ ≪≫ (ModuleCat.extendScalars a).mapIso eJ.symm

/-- Degree zero for the actual pulled-support stalk, with its full ambient scalar action. -/
def comapStalkTorZeroIso
    (d : (I.comap p).subscheme) (j : (I.comap (i ≫ p)).subscheme)
    (hd : i c = (I.comap p).subschemeι d)
    (hj : c = (I.comap (i ≫ p)).subschemeι j) :
    (((Tor (ModuleCat (T.presheaf.stalk (i c))) 0).obj
      ((ModuleCat.restrictScalars
        ((T.presheaf.stalkCongr (.of_eq hd)).hom ≫
          (I.comap p).subschemeι.stalkMap d).hom).obj
        (ModuleCat.of ((I.comap p).subscheme.presheaf.stalk d)
          ((I.comap p).subscheme.presheaf.stalk d)))).obj
      ((ModuleCat.restrictScalars (i.stalkMap c).hom).obj
        (ModuleCat.of (C.presheaf.stalk c) (C.presheaf.stalk c)))) ≅
    (ModuleCat.restrictScalars (i.stalkMap c).hom).obj
      ((ModuleCat.restrictScalars
        ((C.presheaf.stalkCongr (.of_eq hj)).hom ≫
          (I.comap (i ≫ p)).subschemeι.stalkMap j).hom).obj
        (ModuleCat.of ((I.comap (i ≫ p)).subscheme.presheaf.stalk j)
          ((I.comap (i ≫ p)).subscheme.presheaf.stalk j))) :=
  (((Tor (ModuleCat (T.presheaf.stalk (i c))) 0).mapIso
    (comapStalkIsoExtendOpenSection i p I c d j hd hj)).app _) ≪≫
    openSectionStalkTorZeroIsoFlip i p c _

/-- Actual inverse-image support stalks have zero positive Tor against an open section
of a flat projection. No support module is assumed flat. -/
theorem isZero_comapStalkTor_succ [Flat p]
    (d : (I.comap p).subscheme) (j : (I.comap (i ≫ p)).subscheme)
    (hd : i c = (I.comap p).subschemeι d)
    (hj : c = (I.comap (i ≫ p)).subschemeι j) (n : ℕ) :
    IsZero (((Tor (ModuleCat (T.presheaf.stalk (i c))) (n + 1)).obj
      ((ModuleCat.restrictScalars
        ((T.presheaf.stalkCongr (.of_eq hd)).hom ≫
          (I.comap p).subschemeι.stalkMap d).hom).obj
        (ModuleCat.of ((I.comap p).subscheme.presheaf.stalk d)
          ((I.comap p).subscheme.presheaf.stalk d)))).obj
      ((ModuleCat.restrictScalars (i.stalkMap c).hom).obj
        (ModuleCat.of (C.presheaf.stalk c) (C.presheaf.stalk c)))) :=
  IsZero.of_iso (isZero_openSectionStalkTor_succ_flip i p c _ n)
    (((Tor (ModuleCat (T.presheaf.stalk (i c))) (n + 1)).mapIso
      (comapStalkIsoExtendOpenSection i p I c d j hd hj)).app _)

/-- The actual degree-zero comparison at a separately named ambient point. -/
def comapStalkTorZeroIsoOfEq
    (x : T) (d : (I.comap p).subscheme) (j : (I.comap (i ≫ p)).subscheme)
    (hc : x = i c) (hd : x = (I.comap p).subschemeι d)
    (hj : c = (I.comap (i ≫ p)).subschemeι j) :
    (((Tor (ModuleCat (T.presheaf.stalk x)) 0).obj
      ((ModuleCat.restrictScalars
        ((T.presheaf.stalkCongr (.of_eq hd)).hom ≫
          (I.comap p).subschemeι.stalkMap d).hom).obj
        (ModuleCat.of ((I.comap p).subscheme.presheaf.stalk d)
          ((I.comap p).subscheme.presheaf.stalk d)))).obj
      ((ModuleCat.restrictScalars
        ((T.presheaf.stalkCongr (.of_eq hc)).hom ≫ i.stalkMap c).hom).obj
        (ModuleCat.of (C.presheaf.stalk c) (C.presheaf.stalk c)))) ≅
    (ModuleCat.restrictScalars
      ((T.presheaf.stalkCongr (.of_eq hc)).hom ≫ i.stalkMap c).hom).obj
      ((ModuleCat.restrictScalars
        ((C.presheaf.stalkCongr (.of_eq hj)).hom ≫
          (I.comap (i ≫ p)).subschemeι.stalkMap j).hom).obj
        (ModuleCat.of ((I.comap (i ≫ p)).subscheme.presheaf.stalk j)
          ((I.comap (i ≫ p)).subscheme.presheaf.stalk j))) := by
  subst x
  simpa only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp] using comapStalkTorZeroIso i p I c d j hd hj

/-- Positive actual stalk Tor vanishes at any specified incidence image. -/
theorem isZero_comapStalkTor_succ_of_eq [Flat p]
    (x : T) (d : (I.comap p).subscheme) (j : (I.comap (i ≫ p)).subscheme)
    (hc : x = i c) (hd : x = (I.comap p).subschemeι d)
    (hj : c = (I.comap (i ≫ p)).subschemeι j) (n : ℕ) :
    IsZero (((Tor (ModuleCat (T.presheaf.stalk x)) (n + 1)).obj
      ((ModuleCat.restrictScalars
        ((T.presheaf.stalkCongr (.of_eq hd)).hom ≫
          (I.comap p).subschemeι.stalkMap d).hom).obj
        (ModuleCat.of ((I.comap p).subscheme.presheaf.stalk d)
          ((I.comap p).subscheme.presheaf.stalk d)))).obj
      ((ModuleCat.restrictScalars
        ((T.presheaf.stalkCongr (.of_eq hc)).hom ≫ i.stalkMap c).hom).obj
        (ModuleCat.of (C.presheaf.stalk c) (C.presheaf.stalk c)))) := by
  subst x
  simpa only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp] using isZero_comapStalkTor_succ i p I c d j hd hj n

end AlgebraicGeometry.Scheme.Hom
