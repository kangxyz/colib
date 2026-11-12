/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Intersection.AffineLineFiber
public import Colib.Algebra.Category.ModuleCat.Tor.RegularBlock

/-!
# Actual endpoint-cut Tor, with flatness only over the affine-line parameter

The first Tor argument is the full endpoint stalk restricted by the actual
fiber-inclusion stalk map. The second is the actual stalk of a scheme mapping
into the ambient family, restricted by its actual stalk map. Both images are
the specified ambient point, including their explicit equality transports.

The ambient parameter and the support parameter are flat over A1. This makes
the literal singleton `t - a` regular on both rings. Native Tor independence
for one regular element therefore proves that every positive degree vanishes.
No flatness over the higher-dimensional correspondence source is assumed.

The integral-component corollary derives its parameter flatness from the whole
family, using actual generic-point images and the native Dedekind theorem.
This is a local endpoint calculation, not yet graph precomposition.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace RingTheory.Sequence

universe u

namespace AlgebraicGeometry.Scheme.AffineLineFiber

open Stacks.Chow

variable {k : Type u} [Field k] {D E : Scheme.{u}}
  (f : D ⟶ Spec (.of (Polynomial k))) (a : k) (j : E ⟶ D)

/-- The whole actual endpoint/support Tor vanishes in every positive degree.
Flatness is only over A1 and is not imposed on `j` or on the endpoint inclusion. -/
theorem isZero_stalkTor_succ [Flat f] [Flat (j ≫ f)]
    (t : D) (d : fiber f a) (e : E)
    (hd : t = inclusion f a d) (he : t = j e) (n : ℕ) :
    IsZero ((((Tor (ModuleCat (D.presheaf.stalk t)) (n + 1)).obj
      ((ModuleCat.restrictScalars
        ((D.presheaf.stalkCongr (.of_eq hd)).hom ≫ (inclusion f a).stalkMap d).hom).obj
        (ModuleCat.of ((fiber f a).presheaf.stalk d) ((fiber f a).presheaf.stalk d)))).obj
      ((ModuleCat.restrictScalars
        ((D.presheaf.stalkCongr (.of_eq he)).hom ≫ j.stalkMap e).hom).obj
        (ModuleCat.of (E.presheaf.stalk e) (E.presheaf.stalk e))))) := by
  let q := ((D.presheaf.stalkCongr (.of_eq hd)).hom ≫ (inclusion f a).stalkMap d).hom
  let φ := ((D.presheaf.stalkCongr (.of_eq he)).hom ≫ j.stalkMap e).hom
  have hq : Function.Surjective q :=
    (SurjectiveOnStalks.stalkMap_surjective (inclusion f a) d).comp
      (ConcreteCategory.bijective_of_isIso (D.presheaf.stalkCongr (.of_eq hd)).hom).2
  have hk : RingHom.ker q = Ideal.ofList [scalar f a t] := by
    have H (t : D) (hd : t = inclusion f a d) :
        RingHom.ker ((D.presheaf.stalkCongr (.of_eq hd)).hom ≫
          (inclusion f a).stalkMap d).hom = Ideal.ofList [scalar f a t] := by
      subst t
      simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
        Category.id_comp, Ideal.ofList_singleton, inclusion_stalkMap_ker]
    exact H t hd
  have hregular : IsRegular (D.presheaf.stalk t) [scalar f a t] := by
    refine ⟨(isWeaklyRegular_singleton_iff _ _).mpr (scalar_regular f a t), ?_⟩
    rw [Ideal.smul_eq_mul, Ideal.mul_top, ← hk]
    exact (RingHom.ker_ne_top q).symm
  have hsupport : IsWeaklyRegular (E.presheaf.stalk e) ([scalar f a t].map φ) := by
    rw [List.map_singleton, isWeaklyRegular_singleton_iff]
    change IsSMulRegular (E.presheaf.stalk e)
      ((((D.presheaf.stalkCongr (.of_eq he)).hom ≫ j.stalkMap e).hom) (scalar f a t))
    exact (scalar_stalkMap_of_eq f a j e t he).symm ▸ scalar_regular (j ≫ f) a e
  exact ModuleCat.Tor.isZero_of_regularLeadingPair q φ hq [scalar f a t]
    hregular hk hsupport (n + 1) (Nat.zero_lt_succ n)

/-- The parameter-flatness needed above is derived for every actual generic
component of a flat family, without component-flatness over a larger base. -/
theorem isZero_component_stalkTor_succ [Flat f]
    (z : genericPoints D) (t : D) (d : fiber f a)
    (e : (integralComponentAt z.val).subscheme)
    (hd : t = inclusion f a d) (he : t = (integralComponentAt z.val).subschemeι e)
    (n : ℕ) :
    IsZero ((((Tor (ModuleCat (D.presheaf.stalk t)) (n + 1)).obj
      ((ModuleCat.restrictScalars
        ((D.presheaf.stalkCongr (.of_eq hd)).hom ≫ (inclusion f a).stalkMap d).hom).obj
        (ModuleCat.of ((fiber f a).presheaf.stalk d) ((fiber f a).presheaf.stalk d)))).obj
      ((ModuleCat.restrictScalars
        ((D.presheaf.stalkCongr (.of_eq he)).hom ≫
          (integralComponentAt z.val).subschemeι.stalkMap e).hom).obj
        (ModuleCat.of ((integralComponentAt z.val).subscheme.presheaf.stalk e)
          ((integralComponentAt z.val).subscheme.presheaf.stalk e))))) := by
  have := Scheme.Hom.flat_integralComponentAt_to_dedekind f z
  exact isZero_stalkTor_succ f a (integralComponentAt z.val).subschemeι t d e hd he n

end AlgebraicGeometry.Scheme.AffineLineFiber
