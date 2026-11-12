/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Intersection.AffineLineFiber
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.WholeFibers

/-! # The entire polynomial parameter fiber -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Polynomial

universe u

namespace AlgebraicGeometry.Scheme.PolynomialSectionPencil

open AffineLineFiber Stacks.Chow

variable {k : Type u} [Field k] {D : Scheme.{u}} (t : D ⟶ Spec (.of k))

/-- The unchanged second projection of the full polynomial product. -/
abbrev parameterProjection : parameterSpace t ⟶ Spec (.of k[X]) :=
  pullback.snd t (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])))

@[reassoc]
theorem point_comp_polynomialProjection (a : k) :
    point a ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])) = 𝟙 _ := by
  rw [point, ← Spec.map_comp, ← Spec.map_id]
  apply congrArg Spec.map
  ext r
  exact Polynomial.eval_C

/-- The original endpoint is the entire Cartesian fiber. -/
theorem endpoint_isPullback (a : k) :
    IsPullback t (endpoint t a) (point a) (parameterProjection t) where
  w := (endpoint_snd t a).symm
  isLimit' := ⟨PullbackCone.isLimitAux' _ fun s => by
    have hbase : (s.snd ≫ projection t) ≫ t = s.fst := by
      have h := congrArg (fun g => g ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) s.condition
      simpa only [Category.assoc, point_comp_polynomialProjection, Category.comp_id,
        ← pullback.condition, parameterProjection, projection] using h.symm
    refine ⟨s.snd ≫ projection t, hbase, ?_, ?_⟩
    · apply pullback.hom_ext
      · simp only [PullbackCone.mk_snd, Category.assoc, endpoint_projection, Category.comp_id]
      · change (s.snd ≫ projection t) ≫ endpoint t a ≫ parameterProjection t =
          s.snd ≫ parameterProjection t
        rw [endpoint_snd, ← Category.assoc, hbase]
        exact s.condition
    · intro u _ h
      have he := congrArg (fun f => f ≫ projection t) h
      simpa only [PullbackCone.mk_snd, Category.assoc, endpoint_projection,
        Category.comp_id] using he⟩

/-- The entire polynomial endpoint, with its original closed inclusion. -/
def endpointFiberIso (a : k) : D ≅ fiber (parameterProjection t) a :=
  (endpoint_isPullback t a).isoPullback

@[reassoc (attr := simp)]
theorem endpointFiberIso_hom_inclusion (a : k) :
    (endpointFiberIso t a).hom ≫ inclusion (parameterProjection t) a = endpoint t a :=
  (endpoint_isPullback t a).isoPullback_hom_snd

@[reassoc (attr := simp)]
theorem endpointFiberIso_hom_fst (a : k) :
    (endpointFiberIso t a).hom ≫ pullback.fst (point a) (parameterProjection t) = t :=
  (endpoint_isPullback t a).isoPullback_hom_fst

/-- The map between actual scalar fibers of a change of the original scheme. -/
def parameterFiberMap {E : Scheme.{u}} (j : E ⟶ D) (a : k) :
    fiber (parameterProjection (j ≫ t)) a ⟶ fiber (parameterProjection t) a :=
  pullback.map (point a) (parameterProjection (j ≫ t)) (point a) (parameterProjection t)
    (𝟙 _) (parameterMap t j) (𝟙 _) (by simp)
    ((Category.comp_id _).trans (parameterMap_snd t j).symm)

@[reassoc]
theorem endpointFiberIso_hom_parameterFiberMap {E : Scheme.{u}} (j : E ⟶ D) (a : k) :
    (endpointFiberIso (j ≫ t) a).hom ≫ parameterFiberMap t j a =
      j ≫ (endpointFiberIso t a).hom := by
  apply pullback.hom_ext
  · simp only [parameterFiberMap, pullback.map, Category.assoc, pullback.lift_fst,
      Category.comp_id, endpointFiberIso_hom_fst]
  · change (endpointFiberIso (j ≫ t) a).hom ≫ parameterFiberMap t j a ≫
      inclusion (parameterProjection t) a = j ≫ (endpointFiberIso t a).hom ≫
        inclusion (parameterProjection t) a
    simp only [parameterFiberMap, inclusion, pullback.map, pullback.lift_snd,
      endpointFiberIso_hom_inclusion_assoc, endpointFiberIso_hom_inclusion, endpoint_parameterMap]

instance endpoint_isClosedImmersion (a : k) : IsClosedImmersion (endpoint t a) :=
  MorphismProperty.of_isPullback (endpoint_isPullback t a) inferInstance

/-- The endpoint stalk map has the full principal kernel of the original parameter. -/
theorem endpoint_stalkMap_ker (a : k) (x : D) :
    RingHom.ker ((endpoint t a).stalkMap x).hom =
      Ideal.span {scalar (parameterProjection t) a (endpoint t a x)} := by
  have hk : (endpoint t a).ker = (inclusion (parameterProjection t) a).ker := by
    rw [← endpointFiberIso_hom_inclusion t a, Scheme.Hom.ker_comp_of_isIso]
  rw [ker_stalkMap_eq_idealStalk_ker, hk, inclusion_stalk]

/-- The original endpoint stalk is its literal principal quotient. -/
def endpointStalkQuotientEquiv (a : k) (x : D) :
    ((parameterSpace t).presheaf.stalk (endpoint t a x) ⧸
      Ideal.span {scalar (parameterProjection t) a (endpoint t a x)}) ≃+*
        D.presheaf.stalk x :=
  (Ideal.quotEquivOfEq (endpoint_stalkMap_ker t a x).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (SurjectiveOnStalks.stalkMap_surjective (endpoint t a) x))

@[simp]
theorem endpointStalkQuotientEquiv_mk (a : k) (x : D)
    (r : (parameterSpace t).presheaf.stalk (endpoint t a x)) :
    endpointStalkQuotientEquiv t a x (Ideal.Quotient.mk _ r) =
      (endpoint t a).stalkMap x r := rfl

end AlgebraicGeometry.Scheme.PolynomialSectionPencil
