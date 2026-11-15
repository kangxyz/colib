/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ProjectiveBifunctor
public import Mathlib.Algebra.Homology.BifunctorShift
import StacksFrontier.CategoryTheory.Localization.BifunctorCommShiftTwo
public import StacksFrontier.CategoryTheory.Shift.CommShiftTwoPostcomp

/-!
# Two-variable shift coherence of the native projective total

The signed cochain shift comparisons descend along the two homotopy
quotients. Precomposition by the selected projective equivalence and
postcomposition by the native derived quotient retain that coherence in the projective
derived comparison.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

local notation "PST(" K ")" => TransferCoefficients K
local notation "c" => ComplexShape.up ℤ
local notation "Q(" K ")" => HomotopyCategory.quotient PST(K) c
local notation "W(" K ")" => HomologicalComplex.homotopyEquivalences PST(K) c

variable (F : PST(k) ⥤ PST(k) ⥤ PST(k)) [F.Additive] [∀ P, (F.obj P).Additive]

set_option maxHeartbeats 1200000 in
-- Checking the comparison uses both instances of the quotient universal property.
/-- The two original homotopy quotients compare the signed total to its chain-level maps. -/
@[instance_reducible]
def signedTotalHomotopyBifunctorLifting :
    Localization.Lifting₂ Q(k) Q(k) W(k) W(k)
      (F.map₂CochainComplex ⋙ (Functor.whiskeringRight _ _ _).obj Q(k))
      (signedTotalHomotopyBifunctor F) := by
  let B := F.map₂CochainComplex
  refine ⟨NatIso.ofComponents (fun K => NatIso.ofComponents (fun L => Iso.refl _)
    (fun {L L'} g => ?_)) (fun {K K'} f => ?_)⟩
  · change (Q(k)).map ((B.obj K).map g) ≫ 𝟙 _ =
      𝟙 _ ≫ (Q(k)).map ((B.obj K).map g)
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  · apply NatTrans.ext
    funext L
    change (Q(k)).map ((B.map f).app L) ≫ 𝟙 _ =
      𝟙 _ ≫ (Q(k)).map ((B.map f).app L)
    exact (Category.comp_id _).trans (Category.id_comp _).symm

set_option maxHeartbeats 1500000 in
-- The two-variable localization produces the original signed interchange by reducibility.
/-- The native Koszul shift comparisons descend along the original homotopy quotients. -/
instance signedTotalHomotopyBifunctorCommShift₂Int :
    (signedTotalHomotopyBifunctor F).CommShift₂Int := by
  let G := F.map₂CochainComplex ⋙ (Functor.whiskeringRight _ _ _).obj Q(k)
  let : G.CommShift₂Int := inferInstanceAs
    (F.map₂CochainComplex ⋙ (Functor.whiskeringRight _ _ _).obj Q(k)).CommShift₂Int
  let : Localization.Lifting₂ Q(k) Q(k) W(k) W(k) G (signedTotalHomotopyBifunctor F) :=
    signedTotalHomotopyBifunctorLifting F
  exact Functor.CommShift₂.ofLocalizationInt Q(k) Q(k) W(k) W(k) G
    (signedTotalHomotopyBifunctor F)

end AlgebraicGeometry.PresheafWithTransfers
