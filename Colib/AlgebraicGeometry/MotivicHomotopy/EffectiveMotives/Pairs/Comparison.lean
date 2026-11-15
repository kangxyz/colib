/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.Basic

/-!
# Reflection of smooth transfer representables

Reflected transfer representables in degree zero recover the original
smooth motive functor, with its actual graph maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Reflected degree-zero transfer representables recover the existing smooth motive functor. -/
def smoothTransferRepresentableEffectiveIso :
    smoothTransferRepresentable k ⋙ effectiveTransferSheaf k ≅ effectiveSmoothMotive k :=
  NatIso.ofComponents
    (fun X => singleSheafReflectionIso k ((representableLarge k).obj (Cor.mk X)))
    (fun f => singleSheafReflectionIso_naturality k
      ((representableLarge k).map ((Cor.graphFunctor k).map f)))

end AlgebraicGeometry.MotivicHomotopy
