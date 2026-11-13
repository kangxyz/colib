/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.PrincipalSection
public import Colib.AlgebraicGeometry.Morphisms.Smooth.FiniteClosedCurveSupport
import Colib.AlgebraicGeometry.Chow.FiniteFlatFundamental
import Colib.AlgebraicGeometry.Correspondences.Composition.Pushforward
import StacksFrontier.AlgebraicGeometry.Morphisms.Open.Generizing
import StacksFrontier.AlgebraicGeometry.Morphisms.UniversallyOpen.QuasiFiniteDominant

/-!
# Generic images of finite cuts on an integral support

A support finite and dominant over a normal integral relative curve sends
codimension-one points to codimension-one points. A whole section cut
that is finite over the base consequently has only generic images over
the base. The support can be integral with singularities.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Order Stacks.Chow TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

attribute [local instance] specializationOrder

/-- Finiteness, dominance, and normality of the target carry codimension-one
points to codimension-one points on the actual schemes. -/
theorem coheight_eq_one_image_of_finite_dominant
    {P C : Scheme.{u}} [IsIntegral P] [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]
    (f : P ⟶ C) [IsFinite f] [IsDominant f] (x : P) (hx : coheight x = 1) :
    coheight (f x) = 1 := by
  let : UniversallyOpen f := by
    apply universallyOpen_of_locallyQuasiFinite_of_dominant_components f
      isGeometricallyUnibranch_of_isNormal
    intro A
    have hA : (A : Set P) = Set.univ := by
      simpa only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] using A.2
    refine ⟨⟨Set.univ, by simp [irreducibleComponents_eq_singleton]⟩, ?_⟩
    rw [hA, Set.image_univ]
    exact f.denseRange.closure_eq
  have hf := (liftsGeneralizations_iff_generalizingMap f).mp
    (liftsGeneralizations_of_isOpenMap f f.isOpenMap)
  have hle : coheight (f x) ≤ 1 := by
    apply coheight_le_coe_iff.mpr
    intro y hy
    obtain ⟨z, hzx, hfz⟩ := hf (Scheme.le_iff_specializes.mp hy.le)
    have hlt : x < z := lt_of_le_of_ne (Scheme.le_iff_specializes.mpr hzx)
      (fun he ↦ hy.ne ((congrArg (fun a : P ↦ f a) he).trans hfz))
    have hz : coheight z = 0 :=
      Order.lt_one_iff.mp (coheight_le_coe_iff.mp hx.le z hlt)
    have hzg : z ∈ genericPoints P :=
      (mem_genericPoints_iff_isMax P z).mpr (coheight_eq_zero.mp hz)
    have hyg : y ∈ genericPoints C :=
      hfz ▸ mem_genericPoints_of_generalizingMap hf hzg
    rw [coheight_eq_zero.mpr ((mem_genericPoints_iff_isMax C y).mp hyg)]
    exact zero_lt_one
  by_contra hne
  have hzero : coheight (f x) = 0 := Order.lt_one_iff.mp (lt_of_le_of_ne hle hne)
  have hg : f x ∈ genericPoints C :=
    (mem_genericPoints_iff_isMax C (f x)).mpr (coheight_eq_zero.mp hzero)
  have hgen := mem_genericPoints_of_isFinite_image f x hg
  exact one_ne_zero (hx.symm.trans
    (coheight_eq_zero.mpr ((mem_genericPoints_iff_isMax P x).mp hgen)))

open AffineLineFiber

/-- The literal finite zero scheme of a nonzero equation on the integral
support has generic image over the base. The intermediate curve is the
normal smooth relative curve that the support finitely dominates. -/
theorem section_zero_image_mem_genericPoints_of_finite_dominant
    {k : Type u} [Field k] {P C X : Scheme.{u}} [IsIntegral P] [IsNoetherian P]
    [IsIntegral C] [IsNormal C] [IsLocallyNoetherian C]
    (f : P ⟶ C) [IsFinite f] [IsDominant f]
    (p : C ⟶ X) [SmoothOfRelativeDimension 1 p] [IsSeparated p]
    (b : P ⟶ Spec (.of k)) (s : Γ(P, ⊤)) (hs : s ≠ 0)
    [IsFinite (inclusion (sectionToAffineLine b s) 0 ≫ f ≫ p)]
    (x : genericPoints (fiber (sectionToAffineLine b s) 0)) :
    (inclusion (sectionToAffineLine b s) 0 ≫ f ≫ p) x.val ∈ genericPoints X := by
  let : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  let i := inclusion (sectionToAffineLine b s) 0
  let y := (i ≫ f) x.val
  let I := integralComponentAt y
  let : IsIntegral I.subscheme := isIntegral_integralComponentAt y
  have hy : coheight y = 1 :=
    coheight_eq_one_image_of_finite_dominant f (i x.val)
      (section_zero_generic_coheight b s hs x.val x.property)
  have hfin : IsFinite (((integralComponentAt x.val).subschemeι ≫ (i ≫ f)) ≫ p) := by
    simp only [Category.assoc, i]
    infer_instance
  let : IsFinite (I.subschemeι ≫ p) :=
    finiteCyclePushforward_isFinite_integralComponentAt (i ≫ f) p x.val hfin
  have hη : I.subschemeι (genericPoint I.subscheme) = y := genericPointOf_integralComponentAt y
  have hg := image_mem_genericPoints_of_coheight_one_finite_closed_support I.subschemeι p
    (genericPoint I.subscheme) (hη.symm ▸ hy)
  change p y ∈ genericPoints X
  simpa only [hη] using hg

end AlgebraicGeometry.Scheme
