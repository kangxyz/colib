/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Representable
public import Mathlib.CategoryTheory.Square

/-!
# Transfer quotients of smooth pairs

The transfer coefficient of a pair is the cokernel of the actual sheafified
signed representables. Its maps come from the original graph square and the
functorial cokernel.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

variable (k : Type u) [Field k]

local notation "Sm(" field ")" => SmoothSite (Spec (CommRingCat.of field))

/-- The signed transfer representable of a smooth scheme and its graph maps. -/
abbrev smoothTransferRepresentable : Sm(k) ⥤ SheafWithTransfers.{u + 1} k :=
  Cor.graphFunctor k ⋙ transferRepresentable k

/-- The original transfer quotient, functorial in maps of smooth pairs. -/
def transferPairCokernelFunctor : Arrow Sm(k) ⥤ SheafWithTransfers.{u + 1} k :=
  (smoothTransferRepresentable k).mapArrow ⋙ coker (SheafWithTransfers.{u + 1} k)

/-- The transfer sheaf quotient associated to the indicated smooth pair. -/
abbrev transferPairCokernel {U X : Sm(k)} (j : U ⟶ X) : SheafWithTransfers.{u + 1} k :=
  (transferPairCokernelFunctor k).obj (Arrow.mk j)

/-- The map of transfer quotients induced by the original square, with the
vertical arrows as the two inclusions of pairs. -/
abbrev transferPairCokernelMap (sq : Square Sm(k)) :
    transferPairCokernel k sq.f₁₃ ⟶ transferPairCokernel k sq.f₂₄ :=
  (transferPairCokernelFunctor k).map (Arrow.homMk' sq.f₁₂ sq.f₃₄ sq.fac)

/-- The canonical transfer quotient projection, as a natural transformation
on the original category of arrows. -/
def transferPairProjection :
    Arrow.rightFunc ⋙ smoothTransferRepresentable k ⟶ transferPairCokernelFunctor k :=
  let R := smoothTransferRepresentable k
  let C := SheafWithTransfers.{u + 1} k
  Functor.whiskerLeft R.mapArrow (coker.π C)

end AlgebraicGeometry.MotivicHomotopy
