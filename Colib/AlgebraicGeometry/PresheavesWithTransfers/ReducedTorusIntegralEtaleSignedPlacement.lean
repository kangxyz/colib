/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusEtaleCoefficientPlacement
public import Colib.Algebra.Homology.SignedParameterConjugation
public import StacksFrontier.Homology.DerivedIndexing.Extend

/-! # Native integral extension and signed placement of the étale parameter

This uses the actual integral sheafified singular chains and coordinate-insertion map.
Adapted from the verified additive-coefficient signed placement, without changing
its native extension, commutation, or additive-boundary comparisons.
The ordinary signed placement below is not asserted to equal a derived tensor
map or a canonical motivic complex. Those comparisons remain separate obligations.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicSimplex
open AlgebraicGeometry.Scheme
universe u
namespace AlgebraicGeometry.PresheafWithTransfers
variable (k : Type u) [Field k]
local notation "Jₖ" => SmoothSite.etaleTopology (Spec (CommRingCat.of k))
local notation "T" => SmoothSite.Contraction.parameterProduct
  (SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k)))
/-- Evaluate étale sheaves on the original multiplicative-group parameter product. -/
abbrev reducedTorusIntegralEtaleParameterFunctor :
    Sheaf Jₖ (ModuleCat.{u + 1} ℤ) ⥤ Sheaf Jₖ (ModuleCat.{u + 1} ℤ) :=
  (T).sheafPushforwardContinuous _ Jₖ Jₖ

local notation "F" => reducedTorusIntegralEtaleParameterFunctor k
local notation "H" => Functor.mapHomologicalComplex F (ComplexShape.up ℤ)
local notation "e" => ComplexShape.embeddingUpIntLE 0
local notation "L" q:max => Functor.obj (sheafifiedSingularChainsFunctor k Jₖ)
  (reducedTorusIntPresheaf k q)

/-- The actual étale singular chains extended into nonpositive cochain degrees. -/
abbrev reducedTorusIntegralEtaleOrdinaryCochain (q : ℕ) := (L q).extend e

/-- Extend the original chain map, retaining the native extension comparison. -/
def reducedTorusIntegralEtaleParameterCochain (q : ℕ) :
    reducedTorusIntegralEtaleOrdinaryCochain k q ⟶
      (H).obj (reducedTorusIntegralEtaleOrdinaryCochain k (q + 1)) :=
  ((e).extendFunctor _).map (reducedTorusIntegralEtaleParameterMap k q) ≫
    (Stacks.DerivedIndexing.mapExtendIso F e (L (q + 1))).hom

/-- Ordinary weight placement retains the negative cochain shift. -/
abbrev reducedTorusIntegralEtaleOrdinarySigned (q : ℕ) :=
  (reducedTorusIntegralEtaleOrdinaryCochain k q)⟦-(q : ℤ)⟧

/-- The native parameter arrow in adjacent signed weights. -/
def reducedTorusIntegralEtaleParameterSigned (q : ℕ) :
    reducedTorusIntegralEtaleOrdinarySigned k q ⟶
      (H).obj ((reducedTorusIntegralEtaleOrdinarySigned k (q + 1))⟦(1 : ℤ)⟧) :=
  signedParameterArrow H (reducedTorusIntegralEtaleParameterCochain k q)
    (-((q + 1 : ℕ) : ℤ)) (-(q : ℤ)) (by omega) (Iso.refl _) (Iso.refl _)

/-- The signed arrow still contains the original cochain map and additive boundary. -/
theorem reducedTorusIntegralEtaleParameterSigned_eq (q : ℕ) :
    let t : ℤ := -((q + 1 : ℕ) : ℤ)
    let s : ℤ := -(q : ℤ)
    let hs : t + 1 = s := by dsimp [t, s]; omega
    reducedTorusIntegralEtaleParameterSigned k q =
      (shiftFunctor _ s).map (reducedTorusIntegralEtaleParameterCochain k q) ≫
      ((H).commShiftIso s).inv.app (reducedTorusIntegralEtaleOrdinaryCochain k (q + 1)) ≫
      (H).map ((shiftFunctorAdd' _ t 1 s hs).hom.app
        (reducedTorusIntegralEtaleOrdinaryCochain k (q + 1))) := by
  exact signedParameterArrow_refl H (reducedTorusIntegralEtaleParameterCochain k q) _ _ _

end AlgebraicGeometry.PresheafWithTransfers
