/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Cancellation
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.WeightOne
import Colib.Util.References

/-!
# The Tate shift of the reduced torus tensor

The actual tensor with the pointed multiplicative group is shifted
by minus one in the cochain convention of the motivic complex.
On the motive of the base, its coefficient quotient identifies with
the weight-one reduced torus using the literal unit graph.
-/

public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open AlgebraicGeometry.Scheme

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "B" => SmoothSite.base S

variable [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1})]

/-- Tate twist on effective motives, in the convention of the original
signed weight-one motivic complex. -/
def effectiveTateTwist : EffectiveMotivesMinus k ⥤ EffectiveMotivesMinus k :=
  effectiveReducedTorusTensorFunctor k ⋙ shiftFunctor (EffectiveMotivesMinus k) (-1 : ℤ)

/-- The Tate twist of the motive of the base is the original weight-one
complex, with its signed cochain shift. -/
def effectiveTateTwistBaseToMotivicComplexIso :
    (effectiveMotivesMinusToDerived k).obj
        ((effectiveTateTwist k).obj ((effectiveMotive k).obj (Cor.mk B))) ≅
      DerivedCategory.Q.obj (motivicComplex k 1) :=
  let H := effectiveMotivesMinusToDerived k
  let e := effectiveReducedTorusTensorRepresentableIso k (Cor.mk B)
  H.mapIso ((shiftFunctor (EffectiveMotivesMinus k) (-1 : ℤ)).mapIso e) ≪≫
    (H.commShiftIso (-1 : ℤ)).app _ ≪≫ torusCancellationBaseMotivicComplexIso k

/-- Cancellation for the actual weight-one Tate twist of bounded-above
effective motives. -/
@[colib_tag "COL-1046", colib_ref "Voevodsky2010Cancellation" "Corollary 4.10, p. 684"
  "adaptation" "Full faithfulness of the Tate twist on the native bounded-above effective category"]
def effectiveTateTwistFullyFaithful : (effectiveTateTwist k).FullyFaithful :=
  (effectiveReducedTorusTensorFullyFaithful k).comp
    (Functor.FullyFaithful.ofFullyFaithful (shiftFunctor (EffectiveMotivesMinus k) (-1 : ℤ)))

end AlgebraicGeometry.MotivicHomotopy
