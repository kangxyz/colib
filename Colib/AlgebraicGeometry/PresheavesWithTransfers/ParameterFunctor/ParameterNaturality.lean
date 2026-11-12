/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ParameterFunctor

/-! # Natural transformation induced by an actual parameter map -/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme

universe u v

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k] {T T' : SmoothSite (Spec (.of k))}
  [GeometricallyIntegral T.hom] [GeometricallyIntegral T'.hom]

/-- The actual pullback of the parameter is natural in every signed
transfer coefficient. -/
def withParameterPullbackNatTrans (f : T ⟶ T') :
    (withParameterFunctor T' : PresheafWithTransfers.{v} k ⥤ PresheafWithTransfers.{v} k) ⟶
      withParameterFunctor T where
  app P := parameterPullback P f
  naturality _ _ g := (parameterPullback_coefficient_naturality g f).symm

/-- Two original parameter pullbacks compose in the opposite order. -/
theorem withParameterPullbackNatTrans_comp {T'' : SmoothSite (Spec (.of k))}
    [GeometricallyIntegral T''.hom] (f : T ⟶ T') (g : T' ⟶ T'') :
    (withParameterPullbackNatTrans (f ≫ g) :
      (withParameterFunctor T'' : PresheafWithTransfers.{v} k ⥤ _) ⟶ _) =
        withParameterPullbackNatTrans g ≫ withParameterPullbackNatTrans f := by
  apply NatTrans.ext
  funext P
  exact parameterPullback_comp P f g

end AlgebraicGeometry.PresheafWithTransfers
