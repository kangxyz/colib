/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteGenericLabels

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

noncomputable section

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

-- The full original labels survive; injectivity of their image map is not assumed.
example (x : correspondenceLeftImageIncidence f g h i z w v) :
    genericPoints (correspondenceRemainingFiniteModel f g h i z w v x) ≃
      correspondenceRemainingOriginalGenericLabels f g h i z w v x :=
  correspondenceRemainingFiniteGenericEquivOriginal f g h i z w v x

-- Neither reducedness nor integrality enters the native minimal-prime identification.
example [IsSeparated h] (hz : IsFiniteCorrespondencePoint f g z)
    (hw : IsFiniteCorrespondencePoint g h w)
    (x : correspondenceLeftImageIncidence f g h i z w v) :
    {q : PrimeSpectrum (correspondenceRemainingFiniteRing f g h i z w v x) // IsMin q} ≃
      correspondenceRemainingOriginalGenericLabels f g h i z w v x :=
  correspondenceRemainingFiniteMinPrimeEquivOriginal f g h i z w v hz hw x

end

#check Stacks.Chow.correspondenceRemainingOriginalGenericLabels

#check Stacks.Chow.correspondenceRemainingFiniteModel_image_specializes

#check Stacks.Chow.correspondenceRemainingFiniteGenericEquivOriginal

#check Stacks.Chow.correspondenceRemainingFiniteGenericEquivOriginal_val

#check Stacks.Chow.correspondenceRemainingFiniteGenericEquivMinPrime

#check Stacks.Chow.correspondenceRemainingFiniteGenericEquivMinPrime_asIdeal

#check Stacks.Chow.correspondenceRemainingFiniteMinPrimeEquivOriginal
