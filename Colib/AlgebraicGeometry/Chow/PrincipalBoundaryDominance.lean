/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.PrincipalBoundarySupport
public import Colib.AlgebraicGeometry.Morphisms.Smooth.CodimensionOneDominance

/-!
# Genuine component dominance of principal boundary supports

Adapted from `Motivic/Aglib/AlgebraicGeometry/Cycles/Divisors/PrincipalOrder.lean:104-152`
in the 2026-10-21 checkpoint. The cycle and integral support are now the native Stacks
objects. The retained open, not the compactification, is smooth of relative dimension one.
Finiteness is produced by properness and the whole boundary; dominance follows from the
actual finite residue extension and the coheight-one computation in a smooth curve fibre.
No flatness of the closed support is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Order

universe u

namespace Stacks.Chow

variable {C S V : Scheme.{u}} [IsIntegral C] [IsNoetherian C]

/-- A nonzero coefficient of the native principal cycle has integral support whose
actual image is a component of the base. All geometric premises are on the original
proper compactification, retained smooth relative curve and full boundary neighborhood. -/
theorem principalCycle_support_dominates_component
    [IsAffine S] [V.IsQuasiAffine] (q : C ⟶ S) [IsProper q]
    (j : V ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
    (U : C.Opens) [Nonempty U] (hU : (Set.range j)ᶜ ⊆ (U : Set C))
    (f : Γ(C, U)) (hf : IsUnit f) (x : C)
    (hx : principalCycle C (C.germToFunctionField U f) x ≠ 0) :
    Set.range ((integralComponentAt x).subschemeι ≫ q) ∈ irreducibleComponents S := by
  let D := integralComponentAt x
  let d := D.subschemeι
  have : IsIntegral D.subscheme := isIntegral_integralComponentAt x
  have hd : Set.range d ⊆ Set.range j := by
    rw [Scheme.IdealSheafData.range_subschemeι, coe_support_integralComponentAt]
    exact principalCycle_closure_subset_retained j U hU f hf x hx
  let i := IsOpenImmersion.lift j d hd
  have hi : i ≫ j = d := IsOpenImmersion.lift_fac j d hd
  have : IsClosedImmersion (i ≫ j) := by rw [hi]; infer_instance
  have : IsClosedImmersion i := IsClosedImmersion.of_comp i j
  have : IsFinite (d ≫ q) := principalCycle_support_isFinite q j U hU f hf x hx
  have hcomp : i ≫ (j ≫ q) = d ≫ q := by rw [← Category.assoc, hi]
  have : IsFinite (i ≫ (j ≫ q)) := by rw [hcomp]; infer_instance
  let a := genericPoint D.subscheme
  have hda : d a = x := genericPointOf_integralComponentAt x
  have hx1 : coheight x = 1 := by
    by_contra hn
    exact hx (Scheme.ord_eq_zero_of_coheight_neq_one hn _)
  have ha : coheight (i a) = 1 := by
    rw [← coheight_eq_of_isOpenImmersion j]
    change coheight ((i ≫ j) a) = 1
    rw [hi, hda]
    exact hx1
  have hg := Scheme.image_mem_genericPoints_of_coheight_one_finite_closed_support i (j ≫ q) a ha
  have hga : (j ≫ q) (i a) = (d ≫ q) a :=
    congrArg (fun h : D.subscheme ⟶ S => h a) hcomp
  rw [hga] at hg
  have he : closure ({(d ≫ q) a} : Set S) = Set.range (d ≫ q) := by
    simpa only [Set.image_univ, (d ≫ q).isClosedMap.isClosed_range.closure_eq] using
      ((genericPoint_spec D.subscheme).image (d ≫ q).continuous).def
  rwa [genericPoints, Set.mem_ofPred_eq, he] at hg

end Stacks.Chow
