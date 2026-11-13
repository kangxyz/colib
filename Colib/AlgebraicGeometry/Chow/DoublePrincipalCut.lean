/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Chow.PolynomialEndpointEuler
import Colib.RingTheory.Multiplicity.PrincipalEuler.TwoScalars
import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ClosedImmersionBaseChange

/-!
# Commuting principal endpoint cuts at a common support point

At a point of finite colength in the common cut, successive cuts of the
component cycles commute when both equations are regular in the original
stalk and each meets the other's reduced components properly. The closed
pushforwards keep the comparison on the original ambient support. The
Euler calculation retains scalar torsion in the unreduced intermediate
fibres.
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicCycle

open _root_.AlgebraicGeometry.Scheme Scheme.AffineLineFiber Stacks.Chow

variable {k : Type u} [Field k] {D : Scheme.{u}} [IsNoetherian D]

private theorem finiteCyclePushforward_fundamentalCycle_ker {E : Scheme.{u}}
    [IsNoetherian E] (j : E ⟶ D) [IsClosedImmersion j] :
    letI : IsNoetherian j.ker.subscheme := isNoetherian_of_finiteType j.ker.subschemeι
    finiteCyclePushforward j (fundamentalCycle E) =
      finiteCyclePushforward j.ker.subschemeι (fundamentalCycle j.ker.subscheme) := by
  let I := j.ker
  let : IsNoetherian I.subscheme := isNoetherian_of_finiteType I.subschemeι
  obtain ⟨e, he⟩ := exists_iso_of_ker_eq j I.subschemeι (I.ker_subschemeι.symm)
  calc
    _ = finiteCyclePushforward (e.hom ≫ I.subschemeι) (fundamentalCycle E) :=
      DFunLike.congr_fun (finiteCyclePushforward_congr _ _ he.symm) _
    _ = _ := by
      rw [← finiteCyclePushforward_comp_apply, finiteCyclePushforward_fundamentalCycle_iso e]

private theorem finiteCyclePushforward_endpoint_apply_eq_principalEuler {E : Scheme.{u}}
    [IsNoetherian E] (f : D ⟶ Spec (.of (Polynomial k))) (a : k)
    (j : E ⟶ D) [IsClosedImmersion j] (x : D) (hx : x ∈ Set.range (inclusion f a))
    (hfin : Module.length (D.presheaf.stalk x)
      (D.presheaf.stalk x ⧸ (Ideal.span {scalar f a x} ⊔ IdealSheafData.stalk j.ker x)) ≠ ⊤)
    (hproper : ∀ q : PrimeSpectrum (D.presheaf.stalk x),
      q.asIdeal ∈ (IdealSheafData.stalk j.ker x).minimalPrimes → scalar f a x ∉ q.asIdeal) :
    finiteCyclePushforward (inclusion f a)
        (polynomialEndpointMap f a (finiteCyclePushforward j (fundamentalCycle E))) x =
      Module.principalEuler (N := D.presheaf.stalk x ⧸ IdealSheafData.stalk j.ker x)
        (scalar f a x) := by
  obtain ⟨x', rfl⟩ := hx
  rw [finiteCyclePushforward_apply_of_isClosedImmersion,
    finiteCyclePushforward_fundamentalCycle_ker]
  exact polynomialEndpointMap_pushforward_fundamentalCycle_apply_eq_principalEuler
    f a j.ker x' hfin hproper

/-- The actual componentwise endpoint coefficients of two successive cuts
agree in both orders at the original support point. Regularity is imposed
on each original scalar separately. The intermediate stalks can have
embedded scalar torsion. -/
theorem finiteCyclePushforward_polynomialEndpointMap_fundamentalFiber_apply_comm
    (f g : D ⟶ Spec (.of (Polynomial k))) (a b : k) (x : D)
    (hf : x ∈ Set.range (inclusion f a)) (hg : x ∈ Set.range (inclusion g b))
    (hrf : IsSMulRegular (D.presheaf.stalk x) (scalar f a x))
    (hrg : IsSMulRegular (D.presheaf.stalk x) (scalar g b x))
    (hfin : Module.length (D.presheaf.stalk x)
      (D.presheaf.stalk x ⧸ (Ideal.span {scalar f a x} ⊔ Ideal.span {scalar g b x})) ≠ ⊤)
    (hproperf : ∀ q : PrimeSpectrum (D.presheaf.stalk x),
      q.asIdeal ∈ (Ideal.span {scalar g b x}).minimalPrimes → scalar f a x ∉ q.asIdeal)
    (hproperg : ∀ q : PrimeSpectrum (D.presheaf.stalk x),
      q.asIdeal ∈ (Ideal.span {scalar f a x}).minimalPrimes → scalar g b x ∉ q.asIdeal) :
    finiteCyclePushforward (inclusion f a)
        (polynomialEndpointMap f a (finiteCyclePushforward (inclusion g b)
          (fundamentalCycle (fiber g b)))) x =
      finiteCyclePushforward (inclusion g b)
        (polynomialEndpointMap g b (finiteCyclePushforward (inclusion f a)
          (fundamentalCycle (fiber f a)))) x := by
  have hfin' : Module.length (D.presheaf.stalk x)
      (D.presheaf.stalk x ⧸ (Ideal.span {scalar g b x} ⊔ Ideal.span {scalar f a x})) ≠ ⊤ := by
    rw [sup_comm]
    exact hfin
  rw [finiteCyclePushforward_endpoint_apply_eq_principalEuler f a (inclusion g b) x hf
      (by rw [inclusion_stalk]; exact hfin)
      (by simpa only [inclusion_stalk] using hproperf),
    finiteCyclePushforward_endpoint_apply_eq_principalEuler g b (inclusion f a) x hg
      (by rw [inclusion_stalk]; exact hfin')
      (by simpa only [inclusion_stalk] using hproperg), inclusion_stalk, inclusion_stalk]
  exact Module.principalEuler_quotient_span_singleton_comm _ _ hrg hrf

/-- On the first endpoint scheme, its endpoint coefficient of the second
cut agrees with the actual second cut on the components of the first fibre. -/
theorem polynomialEndpointMap_fundamentalFiber_apply_eq_cut
    (f g : D ⟶ Spec (.of (Polynomial k))) (a b : k) (x : fiber f a)
    (hx : inclusion f a x ∈ Set.range (inclusion g b))
    (hrf : IsSMulRegular (D.presheaf.stalk (inclusion f a x)) (scalar f a (inclusion f a x)))
    (hrg : IsSMulRegular (D.presheaf.stalk (inclusion f a x)) (scalar g b (inclusion f a x)))
    (hfin : Module.length (D.presheaf.stalk (inclusion f a x))
      (D.presheaf.stalk (inclusion f a x) ⧸
        (Ideal.span {scalar f a (inclusion f a x)} ⊔
          Ideal.span {scalar g b (inclusion f a x)})) ≠ ⊤)
    (hproperf : ∀ q : PrimeSpectrum (D.presheaf.stalk (inclusion f a x)),
      q.asIdeal ∈ (Ideal.span {scalar g b (inclusion f a x)}).minimalPrimes →
        scalar f a (inclusion f a x) ∉ q.asIdeal)
    (hproperg : ∀ q : PrimeSpectrum (D.presheaf.stalk (inclusion f a x)),
      q.asIdeal ∈ (Ideal.span {scalar f a (inclusion f a x)}).minimalPrimes →
        scalar g b (inclusion f a x) ∉ q.asIdeal) :
    polynomialEndpointMap f a (finiteCyclePushforward (inclusion g b)
        (fundamentalCycle (fiber g b))) x =
      finiteCyclePushforward (inclusion (inclusion f a ≫ g) b)
        (polynomialEndpointMap (inclusion f a ≫ g) b (fundamentalCycle (fiber f a))) x := by
  let i := inclusion f a
  let j := inclusion g b
  let l := inclusion (i ≫ g) b
  let q := fiberMap g b i
  let c := polynomialEndpointMap (i ≫ g) b (fundamentalCycle (fiber f a))
  have h := finiteCyclePushforward_polynomialEndpointMap_fundamentalFiber_apply_comm
    f g a b (i x) ⟨x, rfl⟩ hx hrf hrg hfin hproperf hproperg
  rw [polynomialEndpointMap_pushforward_closed g b i (fundamentalCycle (fiber f a))] at h
  change _ = finiteCyclePushforward j (finiteCyclePushforward q c) (i x) at h
  have hcomp : finiteCyclePushforward (q ≫ j) c = finiteCyclePushforward (l ≫ i) c :=
    DFunLike.congr_fun (finiteCyclePushforward_congr _ _ (fiberMap_inclusion g b i)) c
  rw [finiteCyclePushforward_comp_apply q j c, hcomp,
    ← finiteCyclePushforward_comp_apply l i c] at h
  exact (finiteCyclePushforward_apply_of_isClosedImmersion i _ x).symm.trans
    (h.trans (finiteCyclePushforward_apply_of_isClosedImmersion i
      (finiteCyclePushforward l c) x))

end AlgebraicGeometry.AlgebraicCycle
