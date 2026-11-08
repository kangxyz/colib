module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingExteriorMultiplicity

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

-- Full exterior products need not be reduced; no fibre-length-one hypothesis is supplied.
example [Flat (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)]
    (F : ℕ → (correspondenceIncidence f g h z w).Modules) (s : Finset ℕ)
    (x : correspondenceLeftIntermediateSupportProduct f g h i z w v) :
    ∑ n ∈ s, (-1 : ℤ) ^ n * sheafMultiplicity
      ((Scheme.Modules.pullback (correspondenceLeftExteriorProjection f g h i z w v)).obj
        (F n)) x =
      (∑ n ∈ s, (-1 : ℤ) ^ n *
        sheafMultiplicity (F n) (correspondenceLeftExteriorProjection f g h i z w v x)) *
          (correspondenceLeftExteriorFiberLength f g h i z w v x : ℤ) :=
  sum_signed_sheafMultiplicity_correspondenceLeftExterior_pullback f g h i z w v F s x

-- Every split generic label retains its original label without assuming injectivity.
example [Flat (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)]
    (x : genericPoints (correspondenceLeftIntermediateSupportProduct f g h i z w v)) :
    genericPoints (correspondenceIncidence f g h z w) :=
  correspondenceLeftExteriorGenericLabel f g h i z w v x
