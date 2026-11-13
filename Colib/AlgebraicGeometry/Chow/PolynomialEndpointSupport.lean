/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.PolynomialEndpointCycle
public import Colib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.ParameterFiber
public import Colib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.ParameterGeometry
public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.Base
public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.Codimension
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme

/-! # Codimension of a whole polynomial endpoint support -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Order TopologicalSpace Stacks.Chow

universe u

namespace AlgebraicGeometry.AlgebraicCycle

open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.AffineLineFiber
open _root_.AlgebraicGeometry.Scheme.PolynomialSectionPencil

variable {k : Type u} [Field k] {C : Scheme.{u}} [IsIntegral C] [IsNoetherian C]
  (p : C ⟶ Spec (.of k)) [LocallyOfFiniteType p]

/-- Every nonzero coefficient of a flat component endpoint has coheight one
in the original scheme. -/
theorem polynomialComponentEndpoint_coheight_one (a : k) (z : parameterSpace p)
    (hz : coheight z = 1) [Flat ((integralComponentAt z).subschemeι ≫ parameterProjection p)]
    (x : C) (hx : polynomialComponentEndpoint (parameterProjection p) a z
      ((endpointFiberIso p a).hom x) ≠ 0) : coheight x = 1 := by
  let T := fieldChowSituation k
  let f := parameterProjection p
  let b := projection p ≫ p
  let e := endpointFiberIso p a
  let d := (integralComponentAt z).subschemeι
  let D := (integralComponentAt z).subscheme
  let : IsIntegral D := isIntegral_integralComponentAt z
  let : IsNoetherian D := isNoetherian_of_finiteType_of_isNoetherian d
  let n := relativeDimension T.dimensionFunction b (genericPoint (parameterSpace p))
  have hb : schemeDeltaDimension T b = (n : EInt) :=
    schemeDeltaDimension_eq_genericPoint T b
  have hη : coheight (endpoint p a (genericPoint C)) = 1 := by
    have hg : genericPoint C ∈ genericPoints C := genericPoint_mem_genericPoints C
    have h := ringKrullDim_stalk_eq_one f a ⟨e.hom (genericPoint C),
      mem_genericPoints_of_flat e.hom hg⟩
    have he := congrArg (fun j : C ⟶ parameterSpace p => j (genericPoint C))
      (endpointFiberIso_hom_inclusion p a)
    change inclusion f a (e.hom (genericPoint C)) = endpoint p a (genericPoint C) at he
    rw [ringKrullDim_stalk_eq_coheight, he] at h
    exact_mod_cast h
  have hc : schemeDeltaDimension T p = ((n - 1 : ℤ) : EInt) := by
    have h := relativeDimension_comp_closedImmersion T.dimensionFunction (endpoint p a)
      b (genericPoint C)
    rw [show endpoint p a ≫ b = p by simp only [b, endpoint_projection_assoc]] at h
    rw [schemeDeltaDimension_eq_genericPoint, h,
      relativeDimension_eq_sub_one_of_coheight_eq_one T b hb hη]
  have hd : schemeDeltaDimension T (d ≫ b) = ((n - 1 : ℤ) : EInt) := by
    have he : d (genericPoint D) = z := genericPointOf_integralComponentAt z
    rw [schemeDeltaDimension_eq_genericPoint, relativeDimension_comp_closedImmersion, he,
      relativeDimension_eq_sub_one_of_coheight_eq_one T b hb hz]
  let j := inclusion (d ≫ f) a
  let m := fiberMap f a d
  change finiteCyclePushforward m (fundamentalCycle (fiber (d ≫ f) a)) (e.hom x) ≠ 0 at hx
  obtain ⟨y, hy, hmy⟩ := finiteCyclePushforward_support_subset m _ hx
  have hygen := support_fundamentalCycle_subset (fiber (d ≫ f) a) hy
  have hycodim : coheight (j y) = 1 := by
    have h := ringKrullDim_stalk_eq_one (d ≫ f) a ⟨y, hygen⟩
    rw [ringKrullDim_stalk_eq_coheight] at h
    exact_mod_cast h
  have hpr : inclusion f a ≫ projection p = e.inv := by
    apply (cancel_epi (endpointFiberIso p a).hom).mp
    calc
      _ = endpoint p a ≫ projection p := by
        rw [← Category.assoc, endpointFiberIso_hom_inclusion]
      _ = 𝟙 _ := endpoint_projection p a
      _ = _ := e.hom_inv_id.symm
  have hmap : j ≫ (d ≫ projection p) = m ≫ e.inv := by
    rw [← hpr, ← Category.assoc m, show m ≫ inclusion f a = j ≫ d from fiberMap_inclusion f a d,
      Category.assoc]
  let : IsClosedImmersion (j ≫ (d ≫ projection p)) := hmap.symm ▸
    inferInstanceAs (IsClosedImmersion (m ≫ e.inv))
  have hmapx : (j ≫ (d ≫ projection p)) y = x := by
    rw [hmap, Scheme.Hom.comp_apply, hmy]
    exact congrArg (fun g : C ⟶ C => g x) e.hom_inv_id
  have he := relativeDimension_eq_of_isClosedImmersion_comp T (d ≫ b) p
    (d ≫ projection p) (Category.assoc _ _ _) j y
  change relativeDimension T.dimensionFunction (d ≫ b) (j y) =
    relativeDimension T.dimensionFunction p ((j ≫ (d ≫ projection p)) y) at he
  rw [hmapx, relativeDimension_eq_sub_one_of_coheight_eq_one T (d ≫ b) hd hycodim] at he
  exact (relativeDimension_eq_sub_one_iff_coheight_eq_one T p hc x).mp he.symm

end AlgebraicGeometry.AlgebraicCycle
