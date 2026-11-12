/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.ParameterGraph
import Colib.AlgebraicGeometry.Scheme.CartesianRange
import Colib.CategoryTheory.Limits.Shapes.Pullback.ParameterGraph
import Colib.RingTheory.Polynomial.LaurentEvaluation

/-!
# Regular stalk equation of a torus parameter graph

The native torus product has the literal Laurent chart on an affine
open of the coefficient scheme. In that chart the graph equation is the
original coefficient minus the free coordinate. Its germ is regular
even when the coefficient scheme has nilpotents.
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

open AffineLineFiber Stacks.Chow NativeTorusPolynomial

variable {k : Type u} [Field k] {P : Scheme.{u}} (b : P ⟶ Spec (.of k))

set_option quotPrecheck false in
local notation "τ" => (multiplicativeGroupBaseChange (Spec (.of k)) ↘ Spec (.of k))

local notation "W" => torusParameterScheme b
local notation "π" => pullback.fst b τ

private theorem parameterChart_appTop_equation {R : Type u} [CommRing R]
    (i : Spec (.of R) ⟶ P) (a : (Γ(P, ⊤))ˣ) :
    let j := (nativeChartIso (i ≫ b)).hom ≫ pullbackParameterExtensionMap i b τ
    let r := (Scheme.ΓSpecIso (.of R)).hom (i.appTop a.val)
    j.appTop (torusParameterEquation b a 1) =
      (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv
        (LaurentPolynomial.C r - LaurentPolynomial.T 1) := by
  let e := (nativeChartIso (i ≫ b)).hom
  let ρ := pullbackParameterExtensionMap i b τ
  let r := (Scheme.ΓSpecIso (.of R)).hom (i.appTop a.val)
  let E := Scheme.ΓSpecIso (.of (LaurentPolynomial R))
  have ha : (Scheme.ΓSpecIso (.of R)).inv r = i.appTop a.val :=
    ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of R)).hom_inv_id (i.appTop a.val)
  have hcoeff : (e ≫ ρ).appTop ((pullback.fst b τ).appTop a.val) =
      E.inv (LaurentPolynomial.C r) := by
    calc
      _ = (e ≫ pullback.fst (i ≫ b) τ ≫ i).appTop a.val := by
        rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Category.assoc,
          pullbackParameterExtensionMap_fst]
      _ = e.appTop ((pullback.fst (i ≫ b) τ).appTop (i.appTop a.val)) := by
        simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      _ = _ := by
        rw [← ha]
        exact chartMap_appTop_coefficient (i ≫ b) r
  have hcoord : (e ≫ ρ).appTop (torusParameterCoordinate b).val =
      E.inv (LaurentPolynomial.T 1) := by
    change (e ≫ ρ).appTop ((pullback.snd b τ).appTop
      (multiplicativeGroupBaseChangeCoordinate (Spec (.of k))).val) = _
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Category.assoc,
      pullbackParameterExtensionMap_snd]
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    exact chartMap_appTop_coordinate (i ≫ b)
  change (e ≫ ρ).appTop (torusParameterEquation b a 1) =
    E.inv (LaurentPolynomial.C r - LaurentPolynomial.T 1)
  simp only [torusParameterEquation, Units.val_one, map_one, mul_one, map_sub, hcoeff, hcoord]

/-- The literal torus graph scalar is regular in the original ambient stalk. -/
theorem torusParameterZeroMap_scalar_regular (a : (Γ(P, ⊤))ˣ) (x : W) :
    IsSMulRegular ((W).presheaf.stalk x) (scalar (torusParameterZeroMap b a 1) 0 x) := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top (π x))
  let R := Γ(P, U)
  let i : Spec (.of R) ⟶ P := hU.fromSpec
  let ρ := pullbackParameterExtensionMap i b τ
  let e := (nativeChartIso (i ≫ b))
  let j := e.hom ≫ ρ
  have hpb := pullbackParameterExtension_isPullback i b τ
  let : IsOpenImmersion ρ :=
    MorphismProperty.of_isPullback hpb.flip (inferInstance : IsOpenImmersion i)
  let : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion (e.hom ≫ ρ))
  have hx : x ∈ Set.range ρ := by
    change x ∈ Set.range (pullbackParameterExtensionMap i b τ)
    rw [range_fst_of_isPullback hpb]
    change π x ∈ Set.range i
    rw [show Set.range i = (U : Set P) from hU.range_fromSpec]
    exact hxU
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨z, rfl⟩ := e.hom.surjective y
  let A := LaurentPolynomial R
  let B := (Spec (.of A)).presheaf.stalk z
  let r := (Scheme.ΓSpecIso (.of R)).hom (i.appTop a.val)
  let d : A := LaurentPolynomial.C r - LaurentPolynomial.T 1
  have hreg : IsSMulRegular A d := by
    intro s t heq
    apply LaurentPolynomial.isSMulRegular_T_sub_C r
    change (LaurentPolynomial.T 1 - LaurentPolynomial.C r) • s = _
    apply neg_injective
    simpa only [d, ← neg_sub (LaurentPolynomial.T 1) (LaurentPolynomial.C r), neg_smul] using heq
  let : Algebra A B := (StructureSheaf.toStalk A z).hom.toAlgebra
  have : IsLocalization.AtPrime B z.asIdeal :=
    inferInstanceAs (IsLocalization.AtPrime ((Spec.structureSheaf A).presheaf.stalk z) z.asIdeal)
  let : Module.Flat A B := IsLocalization.flat _ z.asIdeal.primeCompl
  let dₓ : B := StructureSheaf.toStalk A z d
  have hreg' : IsSMulRegular B dₓ := by
    change IsSMulRegular B (algebraMap A B d)
    exact IsSMulRegular.of_flat (S := B) hreg
  have hscalar : j.stalkMap z (scalar (torusParameterZeroMap b a 1) 0 (j z)) = dₓ := by
    rw [sectionToAffineLine_zero_scalar]
    calc
      _ = (Spec (.of A)).presheaf.Γgerm z (j.appTop (torusParameterEquation b a 1)) :=
        j.germ_stalkMap_apply ⊤ z (Opens.mem_top _) _
      _ = _ := by
        have hd : j.appTop (torusParameterEquation b a 1) = (ΓSpecIso (.of A)).inv d :=
          parameterChart_appTop_equation b i a
        rw [hd]
        rfl
  change IsSMulRegular ((W).presheaf.stalk (j z)) (scalar (torusParameterZeroMap b a 1) 0 (j z))
  intro s t hst
  apply (ConcreteCategory.bijective_of_isIso (j.stalkMap z)).1
  apply hreg'
  rw [← hscalar]
  simpa only [smul_eq_mul, map_mul] using congrArg (j.stalkMap z) hst

/-- The exact kernel ideal of the original parameter graph has the original scalar. -/
theorem torusParameterGraph_stalk_ideal (a : (Γ(P, ⊤))ˣ) (x : W) :
    IdealSheafData.stalk (torusParameterGraph b a).ker x =
      Ideal.span {scalar (torusParameterZeroMap b a 1) 0 x} := by
  have h := torusParameterGraphZeroIso_hom_inclusion b a 1
  rw [inv_one, mul_one] at h
  rw [← h, Scheme.Hom.ker_comp_of_isIso, inclusion_stalk]

/-- The actual stalk of the coefficient scheme is the quotient by the
literal graph equation, via the graph inclusion stalk map. -/
def torusParameterGraphStalkQuotientEquiv (a : (Γ(P, ⊤))ˣ) (x : P) :
    ((W).presheaf.stalk (torusParameterGraph b a x) ⧸
      Ideal.span {scalar (torusParameterZeroMap b a 1) 0 (torusParameterGraph b a x)}) ≃+*
        P.presheaf.stalk x := by
  let j := torusParameterGraph b a
  have h : RingHom.ker (j.stalkMap x).hom =
      Ideal.span {scalar (torusParameterZeroMap b a 1) 0 (j x)} := by
    rw [ker_stalkMap_eq_idealStalk_ker]
    exact torusParameterGraph_stalk_ideal b a (j x)
  exact (Ideal.quotEquivOfEq h.symm).trans
    (RingHom.quotientKerEquivOfSurjective (SurjectiveOnStalks.stalkMap_surjective j x))

/-- The quotient equivalence acts by the original graph stalk map. -/
@[simp]
theorem torusParameterGraphStalkQuotientEquiv_mk (a : (Γ(P, ⊤))ˣ) (x : P)
    (r : (W).presheaf.stalk (torusParameterGraph b a x)) :
    torusParameterGraphStalkQuotientEquiv b a x (Ideal.Quotient.mk _ r) =
      (torusParameterGraph b a).stalkMap x r := by
  simp only [torusParameterGraphStalkQuotientEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

set_option quotPrecheck false in
local notation "ξ" => multiplicativeGroupBaseChangeCoordinate (Spec (.of k))

/-- The torus diagonal is the graph of its own coordinate. -/
theorem torusParameterGraph_coordinate_eq_diagonal :
    torusParameterGraph τ ξ = pullback.diagonal τ := by
  apply pullback.hom_ext (f := τ) (g := τ)
  · rw [torusParameterGraph_fst, pullback.diagonal_fst]
  · rw [torusParameterGraph_snd, pullback.diagonal_snd]
    let t : Over.mk τ ⟶ Scheme.asOver (multiplicativeGroupBaseChange (Spec (.of k)))
        (Spec (.of k)) := Over.homMk (𝟙 _) (Category.id_comp _)
    have hu : Units.map t.left.appTop.hom.toMonoidHom ξ = ξ := by
      apply Units.ext
      change (𝟙 _ : multiplicativeGroupBaseChange (Spec (.of k)) ⟶ _).appTop (ξ).val = (ξ).val
      rw [Scheme.Hom.id_appTop, ConcreteCategory.id_apply]
    have h := nativeTorusPoint_recover τ t
    rw [hu] at h
    exact congrArg (fun m => m.left) h

/-- The actual torus diagonal has the literal first-minus-second scalar in
each ambient stalk. -/
theorem torusParameterDiagonal_stalk_ideal (x : torusParameterScheme τ) :
    IdealSheafData.stalk (pullback.diagonal τ).ker x =
      Ideal.span {scalar (torusParameterZeroMap τ ξ 1) 0 x} := by
  rw [← torusParameterGraph_coordinate_eq_diagonal]
  exact torusParameterGraph_stalk_ideal τ ξ x

/-- The diagonal scalar stays regular on the parameter product when the
first variable is free and the second is specified by the coefficient
scheme. The coefficient scheme can be nonreduced. -/
theorem torusParameterDiagonal_scalar_regular_of_product {E : Scheme.{u}}
    (l : P ⟶ multiplicativeGroupBaseChange (Spec (.of k)))
    (e : E ≅ W) (m : E ⟶ torusParameterScheme τ)
    (hf : m ≫ pullback.fst τ τ = e.hom ≫ pullback.snd b τ)
    (hs : m ≫ pullback.snd τ τ = e.hom ≫ π ≫ l) (x : E) :
    IsSMulRegular (E.presheaf.stalk x)
      (m.stalkMap x (scalar (torusParameterZeroMap τ ξ 1) 0 (m x))) := by
  let a := Units.map l.appTop.hom.toMonoidHom ξ
  have h₁ : m.appTop ((pullback.fst τ τ).appTop (ξ).val) =
      e.hom.appTop (torusParameterCoordinate b).val := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hf, Scheme.Hom.comp_appTop]
    rfl
  have h₂ : m.appTop (torusParameterCoordinate τ).val = e.hom.appTop ((π).appTop a.val) := by
    change m.appTop ((pullback.snd τ τ).appTop (ξ).val) =
      e.hom.appTop ((π).appTop (l.appTop (ξ).val))
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hs]
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  have hsec : m.appTop (torusParameterEquation τ ξ 1) =
      -e.hom.appTop (torusParameterEquation b a 1) := by
    simp only [torusParameterEquation, Units.val_one, map_one, mul_one, map_sub, h₁, h₂, neg_sub]
  have hscalar :
      m.stalkMap x (scalar (torusParameterZeroMap τ ξ 1) 0 (m x)) =
        -e.hom.stalkMap x (scalar (torusParameterZeroMap b a 1) 0 (e.hom x)) := by
    rw [sectionToAffineLine_zero_scalar, sectionToAffineLine_zero_scalar]
    calc
      _ = E.presheaf.Γgerm x (m.appTop (torusParameterEquation τ ξ 1)) :=
        m.germ_stalkMap_apply ⊤ x (Opens.mem_top _) _
      _ = -E.presheaf.Γgerm x (e.hom.appTop (torusParameterEquation b a 1)) := by
        rw [hsec, map_neg]
      _ = _ := congrArg Neg.neg (e.hom.germ_stalkMap_apply ⊤ x (Opens.mem_top _) _).symm
  let s := scalar (torusParameterZeroMap b a 1) 0 (e.hom x)
  have hreg : IsSMulRegular (E.presheaf.stalk x) (e.hom.stalkMap x s) := by
    have he := ConcreteCategory.bijective_of_isIso (e.hom.stalkMap x)
    intro y z hyz
    obtain ⟨y', rfl⟩ := he.2 y
    obtain ⟨z', rfl⟩ := he.2 z
    apply congrArg (e.hom.stalkMap x)
    apply torusParameterZeroMap_scalar_regular b a (e.hom x)
    apply he.1
    simpa only [smul_eq_mul, map_mul] using hyz
  rw [hscalar]
  intro y z heq
  apply hreg
  apply neg_injective
  simpa only [neg_smul] using heq

end AlgebraicGeometry.Scheme
