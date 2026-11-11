/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Intersection.AffineLineFiberTor
public import Colib.AlgebraicGeometry.Intersection.FlatProjectionStalkTor

/-!
# Open pieces of an actual endpoint after a flat ambient projection

An actual open map into the full endpoint fiber does not change its local ring.
The composite into the original ambient scheme therefore still has the literal
kernel `(t - a)`. This gives positive native Tor vanishing against every actual
support whose parameter map to A1 is flat.

Combined with the constructed flat-projection comparison, this removes the
extra source factor in the correspondence triple product. The geometric input
is an actual open map to the full endpoint and an equality of scheme morphisms,
not a supplied stalk isomorphism, Tor identity, or endpoint cycle equality.
No support is assumed flat over the correspondence source.

This is the local interface for an individual graph component on a normal
source. The caller must construct its actual open projection and prove the
map equation; this module does not assume those facts for an arbitrary graph.
Implementation provenance: a new native proof toward motivic
`a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/AlgebraicGeometry/Correspondences/Graph/Flat/LeftComposition.lean`.
This is not a byte restoration of that source. It does not infer component
flatness over the full source from whole-family flatness. Native geometric and Tor suppliers
are identified by the precise direct imports and SOURCE_REVIEW.md.

-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits RingTheory.Sequence

universe u

namespace AlgebraicGeometry.Scheme.AffineLineFiber

variable {k : Type u} [Field k] {D E C : Scheme.{u}}
  (f : D ⟶ Spec (.of (Polynomial k))) (a : k) (j : E ⟶ D)
  (o : C ⟶ fiber f a) [IsOpenImmersion o]

/-- The composite of an actual open endpoint piece with the actual inclusion
has precisely the same endpoint kernel, through its literal composite stalk map. -/
theorem open_inclusion_stalkMap_ker (c : C) :
    RingHom.ker ((o ≫ inclusion f a).stalkMap c).hom =
      Ideal.span {scalar f a ((o ≫ inclusion f a) c)} := by
  rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp,
    RingHom.ker_comp_of_injective _
      (ConcreteCategory.bijective_of_isIso (o.stalkMap c)).1]
  exact inclusion_stalkMap_ker f a (o c)

/-- An open piece of the actual endpoint has no positive Tor against an actual
parameter-flat support, with the original ambient stalk action retained. -/
theorem isZero_stalkTor_succ_of_open [Flat f] [Flat (j ≫ f)]
    (c : C) (e : E) (he : (o ≫ inclusion f a) c = j e) (n : ℕ) :
    IsZero ((((Tor (ModuleCat (D.presheaf.stalk ((o ≫ inclusion f a) c)))
      (n + 1)).obj
      ((ModuleCat.restrictScalars ((o ≫ inclusion f a).stalkMap c).hom).obj
        (ModuleCat.of (C.presheaf.stalk c) (C.presheaf.stalk c)))).obj
      ((ModuleCat.restrictScalars
        ((D.presheaf.stalkCongr (.of_eq he)).hom ≫ j.stalkMap e).hom).obj
        (ModuleCat.of (E.presheaf.stalk e) (E.presheaf.stalk e))))) := by
  let q := ((o ≫ inclusion f a).stalkMap c).hom
  let φ := ((D.presheaf.stalkCongr (.of_eq he)).hom ≫ j.stalkMap e).hom
  have hq : Function.Surjective q := by
    rw [show q = (o.stalkMap c).hom.comp ((inclusion f a).stalkMap (o c)).hom by
      simp only [q, Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp]]
    exact (ConcreteCategory.bijective_of_isIso (o.stalkMap c)).2.comp
      (SurjectiveOnStalks.stalkMap_surjective (inclusion f a) (o c))
  have hk : RingHom.ker q = Ideal.ofList [scalar f a ((o ≫ inclusion f a) c)] := by
    rw [Ideal.ofList_singleton]
    exact open_inclusion_stalkMap_ker f a o c
  have hregular : IsRegular (D.presheaf.stalk ((o ≫ inclusion f a) c))
      [scalar f a ((o ≫ inclusion f a) c)] := by
    refine ⟨(isWeaklyRegular_singleton_iff _ _).mpr (scalar_regular f a _), ?_⟩
    rw [Ideal.smul_eq_mul, Ideal.mul_top, ← hk]
    exact (RingHom.ker_ne_top q).symm
  have hsupport : IsWeaklyRegular (E.presheaf.stalk e)
      ([scalar f a ((o ≫ inclusion f a) c)].map φ) := by
    rw [List.map_singleton, isWeaklyRegular_singleton_iff]
    change IsSMulRegular (E.presheaf.stalk e)
      ((((D.presheaf.stalkCongr (.of_eq he)).hom ≫ j.stalkMap e).hom)
        (scalar f a ((o ≫ inclusion f a) c)))
    rw [scalar_stalkMap_of_eq]
    exact scalar_regular (j ≫ f) a e
  exact ModuleCat.Tor.isZero_of_regularLeadingPair q φ hq
    [scalar f a ((o ≫ inclusion f a) c)] hregular hk hsupport
    (n + 1) (Nat.zero_lt_succ n)

variable {T : Scheme.{u}} (p : T ⟶ D) (i : C ⟶ T)
  (hi : i ≫ p = o ≫ inclusion f a) (I : D.IdealSheafData)

/-- Positive Tor vanishes before the actual flat ambient projection when the
projected first map is an actual open piece of the endpoint. Every module is
still the actual support stalk with its literal ambient scalar action. -/
theorem isZero_pulledStalkTor_succ_of_open_endpoint
    [Flat f] [Flat p] [Flat (I.subschemeι ≫ f)]
    (c : C) (d : (I.comap p).subscheme) (e : I.subscheme)
    (hd : i c = (I.comap p).subschemeι d) (he : p (i c) = I.subschemeι e)
    (n : ℕ) :
    IsZero ((((Tor (ModuleCat (T.presheaf.stalk (i c))) (n + 1)).obj
      ((ModuleCat.restrictScalars (i.stalkMap c).hom).obj
        (ModuleCat.of (C.presheaf.stalk c) (C.presheaf.stalk c)))).obj
      ((ModuleCat.restrictScalars
        ((T.presheaf.stalkCongr (.of_eq hd)).hom ≫
          (I.comap p).subschemeι.stalkMap d).hom).obj
        (ModuleCat.of ((I.comap p).subscheme.presheaf.stalk d)
          ((I.comap p).subscheme.presheaf.stalk d))))) := by
  apply Scheme.Hom.isZero_torStalkComap_of_flatProjection p I i c d e hd he (n + 1)
  have H (r : C ⟶ D) (hr : r = o ≫ inclusion f a)
      (he' : r c = I.subschemeι e) :
      IsZero ((((Tor (ModuleCat (D.presheaf.stalk (r c))) (n + 1)).obj
        ((ModuleCat.restrictScalars (r.stalkMap c).hom).obj
          (ModuleCat.of (C.presheaf.stalk c) (C.presheaf.stalk c)))).obj
        ((ModuleCat.restrictScalars
          ((D.presheaf.stalkCongr (.of_eq he')).hom ≫ I.subschemeι.stalkMap e).hom).obj
          (ModuleCat.of (I.subscheme.presheaf.stalk e) (I.subscheme.presheaf.stalk e))))) := by
    subst r
    exact isZero_stalkTor_succ_of_open f a I.subschemeι o c e he' n
  exact H (i ≫ p) hi he

/-- The same vanishing at a separately named ambient incidence point, retaining
both original equality transports. -/
theorem isZero_pulledStalkTor_succ_of_open_endpoint_of_eq
    [Flat f] [Flat p] [Flat (I.subschemeι ≫ f)]
    (c : C) (t : T) (d : (I.comap p).subscheme) (e : I.subscheme)
    (hc : t = i c) (hd : t = (I.comap p).subschemeι d)
    (he : p t = I.subschemeι e) (n : ℕ) :
    IsZero ((((Tor (ModuleCat (T.presheaf.stalk t)) (n + 1)).obj
      ((ModuleCat.restrictScalars
        ((T.presheaf.stalkCongr (.of_eq hc)).hom ≫ i.stalkMap c).hom).obj
        (ModuleCat.of (C.presheaf.stalk c) (C.presheaf.stalk c)))).obj
      ((ModuleCat.restrictScalars
        ((T.presheaf.stalkCongr (.of_eq hd)).hom ≫
          (I.comap p).subschemeι.stalkMap d).hom).obj
        (ModuleCat.of ((I.comap p).subscheme.presheaf.stalk d)
          ((I.comap p).subscheme.presheaf.stalk d))))) := by
  subst t
  simpa only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp] using
      isZero_pulledStalkTor_succ_of_open_endpoint f a o p i hi I c d e hd he n

end AlgebraicGeometry.Scheme.AffineLineFiber
