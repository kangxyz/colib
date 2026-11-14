/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectExactFunctor
public import Colib.CategoryTheory.Waldhausen.GilletWaldhausen.ExactFunctorSequence

/-! # Additivity for short exact sequences of perfect-complex functors

An ambient pointwise short exact sequence of native exact functors determines a
cofibration sequence. The quotient functor's preservation of cofibrations gives
the relative cofibration condition.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.GilletWaldhausen

namespace AlgebraicGeometry.RingedSpace

universe u v w

variable {C : Type v} [Category.{w} C] (V : Structure C) (X : RingedSpace.{u, u})

local notation "P" => IsPerfectComplex (X := X)
local notation "W" => perfectComplexesWaldhausen X

local instance : HasFiniteBiproducts
    (CochainComplex (StrictlyPerfect.OXMod.{u, u, u} X) ℤ) :=
  Abelian.hasFiniteBiproducts (C := CochainComplex (StrictlyPerfect.OXMod.{u, u, u} X) ℤ)

local instance : HasFiniteBiproducts (ObjectProperty.FullSubcategory P) := by
  let := isPerfectComplex_closedUnderFiniteProducts X
  exact ExactSubcategory.subcategoryHasFiniteBiproducts P

/-- The ambient pointwise short exact sequence gives the actual relative cofibrations
and chosen-zero cofiber squares on native perfect complexes. -/
theorem perfectCofibrationSequence_of_shortExact
    {F G H : C ⥤ ObjectProperty.FullSubcategory P} (a : F ⟶ G) (b : G ⟶ H) (z : a ≫ b = 0)
    (hF : IsExact V.cof V.weq (W).cof (W).weq F)
    (hG : IsExact V.cof V.weq (W).cof (W).weq G)
    (hH : IsExact V.cof V.weq (W).cof (W).weq H)
    (hs : ∀ c, ((ShortComplex.mk (a.app c) (b.app c) (NatTrans.congr_app z c)).map
      (ObjectProperty.ι P)).ShortExact) :
    Additivity.IsCofibrationSequence V W a b := by
  let E := ExactSubcategory.exactStructure
    (abelianExactStructure (CochainComplex (StrictlyPerfect.OXMod.{u, u, u} X) ℤ)) P
  have hc (c : C) : E.conflation (exactFunctorSequenceAt a b z c) := hs c
  refine { exactF := hF, exactG := hG, exactH := hH, cofibration := ?_, cofiber := ?_ }
  · have ha (c : C) : (W).cof (a.app c) := (hs c).mono_f
    refine { app_cof := ha, relative_cof := ?_ }
    intro c d f hf
    let m := exactFunctorSequenceMap a b z f
    let : HasPushout (exactFunctorSequenceAt a b z c).f m.τ₁ :=
      Additivity.hasPushout W a ha f
    apply (perfectComplexes_inflation_iff X _).mp
    exact relativePushout_inflation E m (hc c) (hc d)
      ((perfectComplexes_inflation_iff X _).mpr (hH.cofibration f hf))
  · intro c
    exact isPushout_of_isColimit_cokernel _
      (E.cokernel _ (hc c)) (W).isZero _ _

end AlgebraicGeometry.RingedSpace
