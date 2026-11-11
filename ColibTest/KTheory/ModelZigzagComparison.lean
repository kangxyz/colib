/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.KTheory.Bass.ModelZigzagComparison
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u v w
namespace KTheory.Bass.ModelZigzagSequentialization
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
    (M : C ⥤ WideSubcategory preservesZero.{w}) (X : C)
variable (a : ∀ n, vertex Q M X n ⟶ suspendedVertex Q M X n)
    (f : ∀ n, vertex Q M X n ⟶ vertex Q M X (n + 1))
    (H : ∀ n, Homotopy (a n) (f n ≫ unit Q M X n))

example :
    IsStableEquivalence (ZigzagSequentialization.telescopeMap
      (vertex Q M X) (suspendedVertex Q M X) a (unit Q M X) f H) :=
  telescopeMap_isStableEquivalence Q M X a f H

example :
    toStableLocalization.obj (Telescope.prespectrum (vertex Q M X) f) ≅
      toStableLocalization.obj (Telescope.prespectrum
        (ZigzagSequentialization.stage (vertex Q M X) (suspendedVertex Q M X) a (unit Q M X))
        (ZigzagSequentialization.transition (vertex Q M X) (suspendedVertex Q M X) a
          (unit Q M X))) :=
  telescopeIso Q M X a f H

end KTheory.Bass.ModelZigzagSequentialization
end
