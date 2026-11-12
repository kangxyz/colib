/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Principal.GraphEndpointParameter
public import Colib.AlgebraicGeometry.Correspondences.Principal.EndpointTorCuts
public import Colib.AlgebraicGeometry.Correspondences.Principal.GraphIncidenceStalkTor
public import Colib.RingTheory.Multiplicity.PrincipalEuler.SurjectiveCuts

/-!
# Native graph-endpoint Tor and the full parameter cut

The actual structural parameter is regular in the ambient stalk by flatness over
the polynomial line. The integral support only needs a nonzero parameter image.
Actual transported stalk maps supply the quotient-target modules used by native Tor.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.PrincipalFamilyUnitOpen

universe u

namespace Stacks.Chow.PolynomialEndpointFiber

/-- Structural flatness over the polynomial line makes the literal parameter
regular in every ambient stalk, even for a nonreduced ambient scheme. -/
theorem equation_germ_isSMulRegular_of_flat {k : Type u} [Field k] {P : Scheme.{u}}
    (f : P ⟶ Spec (.of (Polynomial k))) [Flat f] (c : k) (x : P) :
    IsSMulRegular (P.presheaf.stalk x)
      (P.presheaf.germ ⊤ x (by trivial) (equation f c)) := by
  let A := (Spec (.of (Polynomial k))).presheaf.stalk (f x)
  let B := P.presheaf.stalk x
  let := (f.stalkMap x).hom.toAlgebra
  have : Module.Flat A B := Flat.stalkMap f x
  let s := (Scheme.ΓSpecIso (.of (Polynomial k))).inv (Polynomial.X - Polynomial.C c)
  have hs : s ≠ 0 := by
    intro hz
    exact Polynomial.X_sub_C_ne_zero c
      ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (Polynomial k))).inv).1
        (hz.trans (map_zero _).symm))
  have hn : (Spec (.of (Polynomial k))).presheaf.germ ⊤ (f x) (by trivial) s ≠ 0 :=
    fun hz => hs ((germ_injective_of_isIntegral _ _ (by trivial))
      (hz.trans (map_zero _).symm))
  have hr : IsSMulRegular A
      ((Spec (.of (Polynomial k))).presheaf.germ ⊤ (f x) (by trivial) s) :=
    fun _ _ h => mul_left_cancel₀ hn h
  have H := hr.of_flat (S := B)
  change IsSMulRegular B (f.stalkMap x
    ((Spec (.of (Polynomial k))).presheaf.germ ⊤ (f x) (by trivial) s)) at H
  have hg : f.stalkMap x
      ((Spec (.of (Polynomial k))).presheaf.germ ⊤ (f x) (by trivial) s) =
        P.presheaf.germ ⊤ x (by trivial) (equation f c) :=
    Scheme.Hom.germ_stalkMap_apply f ⊤ x (by trivial) s
  rwa [hg] at H

end Stacks.Chow.PolynomialEndpointFiber

namespace AlgebraicGeometry.Scheme.Hom

/-- Transporting the base point preserves surjectivity of the actual closed-immersion stalk map. -/
theorem transported_stalkMap_surjective {A P : Scheme.{u}}
    (j : A ⟶ P) [IsClosedImmersion j] (x : P) (a : A) (ha : x = j a) :
    Function.Surjective
      ((P.presheaf.stalkCongr (.of_eq ha)).hom ≫ j.stalkMap a).hom :=
  (j.stalkMap_surjective a).comp (ConcreteCategory.bijective_of_isIso _).2

/-- The kernel of the actual transported stalk map is the full ideal-sheaf stalk. -/
theorem transported_stalkMap_ker {A P : Scheme.{u}}
    (j : A ⟶ P) [IsClosedImmersion j] (x : P) (a : A) (ha : x = j a) :
    RingHom.ker ((P.presheaf.stalkCongr (.of_eq ha)).hom ≫ j.stalkMap a).hom =
      IdealSheafData.stalk j.ker x := by
  subst x
  simpa using (IdealSheafData.stalk_ker_of_isClosedImmersion j a).symm

/-- Germ transport uses the original global-section action of the same map. -/
theorem transported_stalkMap_globalSection {A P : Scheme.{u}}
    (j : A ⟶ P) (x : P) (a : A) (ha : x = j a) (s : Γ(P, ⊤)) :
    ((P.presheaf.stalkCongr (.of_eq ha)).hom ≫ j.stalkMap a).hom
        (P.presheaf.germ ⊤ x (by trivial) s) =
      A.presheaf.germ ⊤ a (by trivial) (j.appTop s) := by
  subst x
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp]
  exact Scheme.Hom.germ_stalkMap_apply j ⊤ a (by trivial) s

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.Chow

variable {k : Type u} [Field k] {X Z E : Scheme.{u}}
  (p : X ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))

/-- The literal graph-endpoint stalk against the actual integral support stalk
has its full principal cut as native Tor Euler coefficient. All scalar actions
are the original transported stalk maps. -/
theorem graphEndpoint_stalkTor_eq_parameterCut [IsIntegral E]
    (c : k) (i : E ⟶ pullback (projection p ≫ p) h) [IsClosedImmersion i]
    [IsDominant (i ≫ pullback.fst (projection p ≫ p) h ≫
      pullback.snd p (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))))]
    (y : pullback (C := Scheme) (projection p ≫ p) h)
    (z : pullback (C := Scheme) p h) (e : E)
    (hy : y = correspondenceGraphFiberAmbientMap p (projection p ≫ p) h
      (endpoint p c) (by simp) z) (he : y = i e) (b : ℕ) :
    let R := (pullback (projection p ≫ p) h).presheaf.stalk y
    let φ := (((pullback (projection p ≫ p) h).presheaf.stalkCongr (.of_eq hy)).hom ≫
      (correspondenceGraphFiberAmbientMap p (projection p ≫ p) h
        (endpoint p c) (by simp)).stalkMap z).hom
    let ψ := (((pullback (projection p ≫ p) h).presheaf.stalkCongr (.of_eq he)).hom ≫
      i.stalkMap e).hom
    (∑ n ∈ Finset.range (b + 1), (-1 : ℤ) ^ n *
      ((Module.length R (((Tor (ModuleCat R) n).obj
        ((ModuleCat.restrictScalars φ).obj
          (ModuleCat.of ((pullback p h).presheaf.stalk z) ((pullback p h).presheaf.stalk z)))).obj
        ((ModuleCat.restrictScalars ψ).obj
          (ModuleCat.of (E.presheaf.stalk e) (E.presheaf.stalk e))))).toNat : ℤ)) =
      ((Module.length (E.presheaf.stalk e) (E.presheaf.stalk e ⧸ Ideal.span
        {E.presheaf.germ ⊤ e (by trivial) (PolynomialEndpointFiber.equation
          (i ≫ pullback.fst (projection p ≫ p) h ≫
            pullback.snd p (Spec.map
              (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))) c)})).toNat : ℤ) := by
  let P := pullback (projection p ≫ p) h
  let α := correspondenceGraphFiberAmbientMap p (projection p ≫ p) h
    (endpoint p c) (by simp)
  let q := pullback.fst (projection p ≫ p) h ≫
    pullback.snd p (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))
  let R := P.presheaf.stalk y
  let φ := ((P.presheaf.stalkCongr (.of_eq hy)).hom ≫ α.stalkMap z).hom
  let ψ := ((P.presheaf.stalkCongr (.of_eq he)).hom ≫ i.stalkMap e).hom
  let n := P.presheaf.germ ⊤ y (by trivial) (PolynomialEndpointFiber.equation q c)
  let : IsClosedImmersion α := by
    have H := (graphEndpoint_parameter_isPullback p h c).flip
    rw [show α = H.isoPullback.hom ≫ PolynomialEndpointFiber.fiberInclusion q c from
      H.isoPullback_hom_snd.symm]
    infer_instance
  have hφ := α.transported_stalkMap_surjective y z hy
  have hψ := i.transported_stalkMap_surjective y e he
  have hker : RingHom.ker φ = Ideal.span {n} := by
    rw [Scheme.Hom.transported_stalkMap_ker α y z hy]
    exact graphEndpoint_ker_stalk_eq_parameter p h c y
  have hreg : IsSMulRegular R n :=
    PolynomialEndpointFiber.equation_germ_isSMulRegular_of_flat q c y
  have hnm : n ∈ IsLocalRing.maximalIdeal R := by
    apply IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top φ)
    rw [hker]
    exact Ideal.subset_span (Set.mem_singleton n)
  have hψn : ψ n = E.presheaf.germ ⊤ e (by trivial)
      (PolynomialEndpointFiber.equation (i ≫ q) c) := by
    rw [Scheme.Hom.transported_stalkMap_globalSection i y e he]
    simp only [q, PolynomialEndpointFiber.equation_comp]
  have hnonzero : ψ n ≠ 0 := by
    rw [hψn]
    exact fun hz => PolynomialEndpointFiber.equation_ne_zero_of_isDominant (i ≫ q) c
      ((germ_injective_of_isIntegral E e (by trivial)) (hz.trans (map_zero _).symm))
  have H := Module.sum_tor_surjective_principal_cut φ hφ ψ hψ n hreg hnm hker hnonzero b
  rw [hψn] at H
  exact H

/-- The original native graph-incidence Tor coefficient is the full parameter
cut on the original integral right support. No support flatness, endpoint-cycle
equality, or comparison of coefficients is an input. -/
@[colib_tag "COL-1070"]
theorem graphIncidenceTorCoefficient_eq_parameterCut
    [IsIntegral X] [IsSeparated p] [Smooth p] [Smooth h]
    (c : k) (s : genericPoints X)
    (w : pullback (C := Scheme) (projection p ≫ p) h)
    [IsDominant ((integralComponentAt w).subschemeι ≫
      pullback.fst (projection p ≫ p) h ≫
        pullback.snd p (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))))]
    (t : genericPoints (correspondenceIncidence p (projection p ≫ p) h
      (correspondenceGraphMap p (projection p ≫ p) (endpoint p c) (by simp) s.val) w)) :
    correspondenceIncidenceTorCoefficient k p (projection p ≫ p) h
      (correspondenceGraphMap p (projection p ≫ p) (endpoint p c) (by simp) s.val) w t =
      ((Module.length
        ((integralComponentAt w).subscheme.presheaf.stalk (pullback.snd (C := Scheme) _ _ t.val))
        ((integralComponentAt w).subscheme.presheaf.stalk (pullback.snd (C := Scheme) _ _ t.val) ⧸
          Ideal.span {((integralComponentAt w).subscheme.presheaf.germ ⊤
            (pullback.snd (C := Scheme) _ _ t.val) (by trivial)
            (PolynomialEndpointFiber.equation ((integralComponentAt w).subschemeι ≫
              pullback.fst (projection p ≫ p) h ≫
                pullback.snd p (Spec.map
                  (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))) c))})).toNat : ℤ) := by
  let := isIntegral_integralComponentAt w
  have := PrincipalFamilyEndpointCuts.projection_smoothOfRelativeDimension p
  have : Smooth (projection p) := SmoothOfRelativeDimension.smooth 1 _
  have : Smooth (projection p ≫ p) := inferInstance
  have : IsAffineHom (projection p) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @IsAffineHom) (IsPullback.of_hasPullback _ _).flip inferInstance
  have : IsSeparated (projection p ≫ p) := inferInstance
  let : IsClosedImmersion (endpoint p c) := by
    have H := (endpoint_parameter_isPullback p c).flip
    rw [← H.isoPullback_hom_snd]
    infer_instance
  let δ := correspondenceGraphMap p (projection p ≫ p) (endpoint p c) (by simp) s.val
  let x := correspondenceIncidenceInclusion p (projection p ≫ p) h δ w t.val
  let l := correspondenceIncidenceToLeftPulled p (projection p ≫ p) h δ w t.val
  have hx := correspondenceIncidence_leftPulled_point_eq p (projection p ≫ p) h δ w t.val
  let y := pullback.snd (pullback.snd p (projection p ≫ p))
    (pullback.fst (projection p ≫ p) h) x
  let z := (leftGraphPulledOuterIso p (projection p ≫ p) h (endpoint p c) (by simp) s).hom l
  have hy := leftGraphPulledOuterIso_point p (projection p ≫ p) h (endpoint p c) (by simp)
    s x l hx
  have he := graphIncidence_right_point p (projection p ≫ p) h (endpoint p c) (by simp)
    s w t.val
  have H := graphEndpoint_stalkTor_eq_parameterCut p h c (integralComponentAt w).subschemeι
    y z (pullback.snd (C := Scheme) _ _ t.val) hy he
    (correspondenceIncidenceTorDegreeBound k p (projection p ≫ p) h δ w t.val)
  rw [correspondenceIncidenceTorCoefficient_eq_sum]
  rw [← H]
  apply Finset.sum_congr rfl
  intro n _
  congr 2
  exact congrArg ENat.toNat (graphIncidenceTor_length_eq_endpointStalkTor
    k p (projection p ≫ p) h (endpoint p c) (by simp) s w t.val n)

end Stacks.Chow
