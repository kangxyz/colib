/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Norm.QuotientLength
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.FiberMaximalSpectrum
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineCoordinateRing
public import StacksFrontier.AlgebraicGeometry.Spaces.ElementaryChartFibre
public import StacksFrontier.RingTheory.Depth.PrincipalDivisorDepthDimension
public import StacksFrontier.RingTheory.Length.RingEquiv

/-!
# The exact stalk length of a norm on a finite free affine chart

The determinant length counts the original principal zero scheme with
its full local multiplicities and the original residue degrees. The
finite source may be disconnected.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Order
open scoped Pointwise

universe u

namespace AlgebraicGeometry.Scheme

private theorem length_stalk_quotient_span_eq_length_atPrime {X : Scheme.{u}}
    [IsAffine X] (x : X) (s : Γ(X, ⊤)) :
    let q := ((isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩).asIdeal
    Module.length (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ Ideal.span {X.presheaf.germ ⊤ x trivial s}) =
      Module.length (Localization.AtPrime q)
        (Localization.AtPrime q ⧸ Ideal.span {algebraMap Γ(X, ⊤) (Localization.AtPrime q) s}) := by
  let q := (isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩
  let Q := Localization.AtPrime q.asIdeal
  let : Algebra Γ(X, ⊤) (X.presheaf.stalk x) := (X.presheaf.germ ⊤ x trivial).hom.toAlgebra
  let : IsLocalization.AtPrime (X.presheaf.stalk x) q.asIdeal :=
    (isAffineOpen_top X).isLocalization_stalk ⟨x, trivial⟩
  let e := IsLocalization.algEquiv q.asIdeal.primeCompl Q (X.presheaf.stalk x)
  have he : e.toRingEquiv.toRingHom (algebraMap Γ(X, ⊤) Q s) =
      X.presheaf.germ ⊤ x trivial s := e.commutes s
  have h := Module.quotient_length_eq_of_ringEquiv e.toRingEquiv
    (Ideal.span {algebraMap Γ(X, ⊤) Q s})
  rw [Ideal.map_span, Set.image_singleton, he] at h
  exact h.symm

private theorem length_stalk_quotient_span_eq_localizedLength {X : Scheme.{u}}
    [IsAffine X] (x : X) (s : Γ(X, ⊤)) :
    let q := ((isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩).asIdeal
    Module.length (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ Ideal.span {X.presheaf.germ ⊤ x trivial s}) =
      Module.length (Localization.AtPrime q)
        (LocalizedModule q.primeCompl (Γ(X, ⊤) ⧸ Ideal.span {s})) := by
  let q := (isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩
  let Q := Localization.AtPrime q.asIdeal
  have hl := (Stacks.RingTheory.PrincipalDivisorDepth.localizedQuotientEquiv s q).length_eq
  change Module.length Q (LocalizedModule q.asIdeal.primeCompl (Γ(X, ⊤) ⧸ Ideal.span {s})) =
    Module.length Q (Q ⧸ ((algebraMap Γ(X, ⊤) Q s) • (⊤ : Submodule Q Q))) at hl
  rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_top_eq_map, Algebra.algebraMap_self,
    Ideal.map_id, Submodule.restrictScalars_self] at hl
  exact (length_stalk_quotient_span_eq_length_atPrime x s).trans hl.symm

/-- The norm equation at a codimension-one point has the sum of the full
source lengths with their original residue degrees. -/
theorem stalkQuotientLength_norm_eq_finsum_fibre {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] (y : Y) (hy : coheight y = 1) (s : Γ(X, ⊤))
    (hs : _root_.IsRegular s) :
    letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    ∀ [Module.Free Γ(Y, ⊤) Γ(X, ⊤)],
      Module.length (Y.presheaf.stalk y)
          ((Y.presheaf.stalk y) ⧸
            Ideal.span {Y.presheaf.germ ⊤ y trivial (Algebra.norm Γ(Y, ⊤) s)}) =
        ∑ᶠ x ∈ {x : X | f x = y},
          (f.residueDegree x : ℕ∞) *
            Module.length (X.presheaf.stalk x)
              ((X.presheaf.stalk x) ⧸ Ideal.span {X.presheaf.germ ⊤ x trivial s}) := by
  dsimp only
  let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  let : Nonempty (⊤ : Y.Opens) := ⟨⟨y, trivial⟩⟩
  let : IsDomain Γ(Y, ⊤) := IsIntegral.component_integral _
  let : IsNoetherianRing Γ(Y, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
  let : Module.Finite Γ(Y, ⊤) Γ(X, ⊤) := f.finite_appTop
  intro hfree
  let : Module.Free Γ(Y, ⊤) Γ(X, ⊤) := hfree
  let p₀ (t : Y) := (isAffineOpen_top Y).primeIdealOf ⟨t, trivial⟩
  let q₀ (x : X) := (isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩
  let p := (p₀ y).asIdeal
  have hp : p.height = 1 := height_primeIdealOf_eq_one hy
  have hcomap (x : X) :
      (q₀ x).asIdeal.comap (algebraMap Γ(Y, ⊤) Γ(X, ⊤)) = (p₀ (f x)).asIdeal := by
    have h := IsAffineOpen.comap_primeIdealOf_appLE (f := f) ⊤ (isAffineOpen_top Y) ⊤
      (isAffineOpen_top X) le_top (x := x) trivial
    have happ : f.appLE ⊤ ⊤ le_top = f.appTop := Hom.appLE_eq_app f
    rw [happ] at h
    exact congrArg PrimeSpectrum.asIdeal h
  have hinjP : Function.Injective p₀ := fun x x' he ↦
    congrArg Subtype.val ((isAffineOpen_top Y).primeIdealOf_injective he)
  have hinjQ : Function.Injective q₀ := fun x x' he ↦
    congrArg Subtype.val ((isAffineOpen_top X).primeIdealOf_injective he)
  have hbij : Set.BijOn q₀ {x : X | f x = y}
      {q : PrimeSpectrum Γ(X, ⊤) | q.asIdeal.comap (algebraMap Γ(Y, ⊤) Γ(X, ⊤)) = p} := by
    refine ⟨?_, hinjQ.injOn, ?_⟩
    · intro x hx
      exact (hcomap x).trans (congrArg (fun t ↦ (p₀ t).asIdeal) hx)
    · intro q hq
      obtain ⟨x, rfl⟩ := (isAffineOpen_top X).primeIdealOf_surjective q
      refine ⟨x.val, ?_, rfl⟩
      exact hinjP (PrimeSpectrum.ext ((hcomap x.val).symm.trans hq))
  have hdeg (x : X) (hx : f x = y) :
      Stacks.Length.primeResidueDegree (algebraMap Γ(Y, ⊤) Γ(X, ⊤)) p (q₀ x).asIdeal =
        f.residueDegree x := by
    subst y
    change Stacks.Length.primeResidueDegree f.appTop.hom (p₀ (f x)).asIdeal (q₀ x).asIdeal =
      f.residueDegree x
    simpa only [p₀, q₀, comap_germ_maximalIdeal_eq_primeIdealOf] using
      primeResidueDegree_comap_germ_eq_residueDegree f x
  rw [length_stalk_quotient_span_eq_length_atPrime y]
  refine (Algebra.length_quotient_span_norm_eq_finsum_fibre p hp s hs).trans ?_
  symm
  refine finsum_mem_eq_of_bijOn q₀ hbij (fun x hx ↦ ?_)
  rw [hdeg x hx, length_stalk_quotient_span_eq_localizedLength x s]

end AlgebraicGeometry.Scheme
