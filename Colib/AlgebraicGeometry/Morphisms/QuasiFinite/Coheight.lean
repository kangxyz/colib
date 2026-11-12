/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.FunctionFieldMap
public import Mathlib.Order.KrullDimension

/-!
# Codimension one above a quasi-finite dominant map

Discrete fibres prevent a strict specialization chain from collapsing. For an
integral dominant map, a point over codimension one is not generic, so the
coheight bound is an equality. No flatness or normality is required.
-/

@[expose] public noncomputable section

open TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A locally quasi-finite map preserves strict specialization chains. -/
theorem Scheme.Hom.strictMono_of_locallyQuasiFinite {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] : StrictMono f := by
  intro a b hab
  refine lt_iff_le_not_ge.mpr ⟨hab.le.map f.continuous, ?_⟩
  intro hba
  have heq : f a = f b := ((hab.le.map f.continuous).antisymm hba).eq.symm
  let : DiscreteTopology (f ⁻¹' {f a}) :=
    isDiscrete_iff_discreteTopology.mp (f.isDiscrete_preimage_singleton (f a))
  have hsub : (⟨b, heq.symm⟩ : f ⁻¹' {f a}) ⤳ ⟨a, rfl⟩ :=
    (subtype_specializes_iff _ _).mpr hab.le
  have h := congrArg Subtype.val (specializes_iff_eq.mp hsub)
  exact (ne_of_lt hab) h.symm

/-- Every point above codimension one is codimension one under an integral
dominant locally quasi-finite map. This supplies the fibre condition in the
finite principal-cut projection formula. -/
theorem Scheme.Hom.coheight_eq_one_of_locallyQuasiFinite {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [LocallyQuasiFinite f] [IsDominant f]
    (x : X) (hx : Order.coheight (f x) = 1) : Order.coheight x = 1 := by
  have hle := Order.coheight_le_coheight_apply_of_strictMono f
    f.strictMono_of_locallyQuasiFinite x
  rw [hx] at hle
  have hne : Order.coheight x ≠ 0 := by
    intro hz
    have hm := Order.coheight_eq_zero.mp hz
    have hgen : x = genericPoint X :=
      (Specializes.antisymm (hm (genericPoint_specializes x))
        (genericPoint_specializes x)).eq
    have hfgen : f (genericPoint X) = genericPoint Y :=
      ((tfae_isDominant_of_isIntegral f).out 1 2).mp (inferInstance : IsDominant f)
    rw [hgen, hfgen] at hx
    have hzero : Order.coheight (genericPoint Y) = 0 :=
      Order.coheight_eq_zero.mpr fun z _ => genericPoint_specializes z
    rw [hzero] at hx
    exact zero_ne_one hx
  exact le_antisymm hle (Order.one_le_iff_ne_zero.mpr hne)

end AlgebraicGeometry
