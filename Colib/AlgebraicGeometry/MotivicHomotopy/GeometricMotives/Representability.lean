/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.LiteralSingleReflection
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Representable

/-!
# Representability by a smooth motive

The effective motive of a smooth scheme is the reflection of its original
sheafified transfer representable. The adjunction computes maps into any
effective motive by maps out of this sheaf in the original derived category.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "NST" => LargeSheaves k
local notation "V" => DerivedCategory.Minus.ι (C := NST)
local notation "J" => effectiveMotivesMinusToDerived k
local notation "I" => effectiveMotivesMinusInclusion k

/-- Maps out of the effective motive of a smooth scheme are the original
derived maps from its degree-zero sheafified transfer representable. -/
def effectiveMotiveDerivedHomEquiv (X : Cor k) (K : EffectiveMotivesMinus k) :
    ((effectiveMotive k).obj X ⟶ K) ≃+
      ((DerivedCategory.singleFunctor NST 0).obj ((transferRepresentable k).obj X) ⟶
        (J).obj K) := by
  let P := (representableLarge k).obj X
  let R := (transferRepresentable k).obj X
  let A := DerivedCategory.Minus.ofCochainComplex
    ((CochainComplex.singleFunctor NST 0).obj R) 0
  let e : (effectiveReflection k).obj A ≅ (effectiveMotive k).obj X :=
    singleSheafReflectionIso k P
  let d : (DerivedCategory.singleFunctor NST 0).obj R ≅ (V).obj A :=
    (DerivedCategory.singleFunctorIsoCompQ NST 0).app R
  let adj := effectiveReflectionAdjunction k
  let v := Functor.FullyFaithful.ofFullyFaithful V
  refine AddEquiv.mk' (e.symm.homFromEquiv.trans
    ((adj.homEquiv A K).trans (v.homEquiv.trans d.symm.homFromEquiv))) ?_
  intro f g
  change d.hom ≫ (V).map (adj.homEquiv A K (e.hom ≫ (f + g))) =
    (d.hom ≫ (V).map (adj.homEquiv A K (e.hom ≫ f))) +
      (d.hom ≫ (V).map (adj.homEquiv A K (e.hom ≫ g)))
  simp only [Adjunction.homEquiv_unit, Preadditive.comp_add, Functor.map_add]

/-- The comparison commutes with the actual maps of effective coefficients. -/
theorem effectiveMotiveDerivedHomEquiv_comp (X : Cor k) {K L : EffectiveMotivesMinus k}
    (f : (effectiveMotive k).obj X ⟶ K) (g : K ⟶ L) :
    effectiveMotiveDerivedHomEquiv k X L (f ≫ g) =
      effectiveMotiveDerivedHomEquiv k X K f ≫ (J).map g := by
  let R := (transferRepresentable k).obj X
  let A := DerivedCategory.Minus.ofCochainComplex
    ((CochainComplex.singleFunctor NST 0).obj R) 0
  let e : (effectiveReflection k).obj A ≅ (effectiveMotive k).obj X :=
    singleSheafReflectionIso k ((representableLarge k).obj X)
  let d : (DerivedCategory.singleFunctor NST 0).obj R ≅ (V).obj A :=
    (DerivedCategory.singleFunctorIsoCompQ NST 0).app R
  let adj := effectiveReflectionAdjunction k
  change d.hom ≫ (V).map (adj.homEquiv A L (e.hom ≫ (f ≫ g))) =
    (d.hom ≫ (V).map (adj.homEquiv A K (e.hom ≫ f))) ≫ (V).map ((I).map g)
  have h := adj.homEquiv_naturality_right (e.hom ≫ f) g
  rw [Category.assoc] at h
  rw [h, (V).map_comp, Category.assoc]

end AlgebraicGeometry.MotivicHomotopy
