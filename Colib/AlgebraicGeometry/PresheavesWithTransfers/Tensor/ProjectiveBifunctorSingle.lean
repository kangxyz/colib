/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ProjectiveBifunctor
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ProjectiveCoefficientSingle
import StacksFrontier.Homology.TensorComplex.BifunctorSingleRightComplex

/-!
# Signed totalization with a degree-zero right argument

With one input concentrated in degree zero, the native signed totalization
reduces to the termwise application of the right-parameter functor.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u w

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

local notation "PST(" K ")" => TransferCoefficients K
local notation "c" => ComplexShape.up ℤ
local notation "S(" K ")" => CochainComplex.singleFunctor PST(K) (0 : ℤ)

variable (F : PST(k) ⥤ PST(k) ⥤ PST(k)) [F.Additive] [∀ P, (F.obj P).Additive]

local instance (P : PST(k)) : (F.flip.obj P).Additive where
  map_add := by
    intro X Y f g
    change (F.map (f + g)).app P = (F.map f).app P + (F.map g).app P
    exact NatTrans.congr_app (F.map_add (f := f) (g := g)) P

/-- The right-parameter comparison is natural in the left cochain complex. -/
def mapBifunctorSingleRightNatIso (P : PST(k)) :
    (F.map₂CochainComplex).flip.obj ((S(k)).obj P) ≅ (F.flip.obj P).mapHomologicalComplex c :=
  NatIso.ofComponents (fun K => mapBifunctorSingleRightIso F K P)
    (fun f => mapBifunctorSingleRightIso_hom_naturality F _ P f)

/-- The comparison descends along the original homotopy quotient. -/
def signedTotalHomotopySingleRightIso (P : PST(k)) :
    (signedTotalHomotopyBifunctor F).flip.obj
        ((HomotopyCategory.quotient PST(k) c).obj ((S(k)).obj P)) ≅
      (F.flip.obj P).mapHomotopyCategory c :=
  CategoryTheory.Quotient.natIsoLift _
    (Functor.isoWhiskerRight (mapBifunctorSingleRightNatIso F P)
      (HomotopyCategory.quotient PST(k) c))

variable [HasDerivedCategory.{w} PST(k)]

/-- The projective comparison after forgetting the bound. -/
def projectiveHomotopySingleRightIso (A : PST(k)) [Projective A] :
    (projectiveHomotopyBifunctorToDerivedMinus F).flip.obj (singleProjective A 0) ≅
      projectiveHomotopyMapToDerivedMinus k (F.flip.obj A) := by
  let ff := Functor.FullyFaithful.ofFullyFaithful (DerivedCategory.Minus.ι (C := PST(k)))
  apply (ff.whiskeringRight _).preimageIso
  exact Functor.isoWhiskerLeft (boundedAboveProjectiveCondition k).ι
    (Functor.isoWhiskerRight (signedTotalHomotopySingleRightIso F A) DerivedCategory.Qh)

/-- A derived signed total with a projective degree-zero coefficient is computed termwise. -/
def projectiveDerivedMinusBifunctorSingleRightIso (A : PST(k)) [Projective A] :
    (projectiveDerivedMinusBifunctor F).flip.obj ((singleDerivedMinus k 0).obj A) ≅
      projectiveDerivedMinusFunctor k (F.flip.obj A) :=
  let E := boundedAboveProjectiveEquivalence k
  let B := projectiveHomotopyBifunctorToDerivedMinus F
  Functor.isoWhiskerLeft E.inverse
    (B.flip.mapIso (singleProjectiveComparison A 0) ≪≫ projectiveHomotopySingleRightIso F A)

end AlgebraicGeometry.PresheafWithTransfers
