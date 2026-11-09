/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingImageExteriorSquare
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.CoherentSheafCycle
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.Support
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Basic

/-!
# Original G,H generic labels and full first-support exterior multiplicity

All original labels are retained under the actual second projection. Flatness is
only the base change of the first support over the original base, automatic over
an arbitrary field. It is never flatness of that support over Y. The closed fibre
is not reduced; its length retains inseparable and nilpotent multiplicities.
Native Stacks 02M1 applies to each coefficient before summing Tor signs.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- Every exterior generic label maps to its original G,H generic label. -/
def correspondenceRightExteriorGenericLabel
    [Flat (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g)]
    (x : genericPoints (correspondenceRightIntermediateSupportProduct f g h i z w v)) :
    genericPoints (correspondenceIncidence g h i w v) := by
  let π := correspondenceRightExteriorProjection f g h i z w v
  let : Flat π := by dsimp [π, correspondenceRightExteriorProjection]; infer_instance
  exact ⟨π x.1, π.mem_genericPoints_of_flat x.2⟩

/-- The full actual closed-fibre length; no value-one or reducedness replacement. -/
def correspondenceRightExteriorFiberLength
    (x : correspondenceRightIntermediateSupportProduct f g h i z w v) : ℕ :=
  (Module.length
    ((correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk x)
    ((correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk x ⧸
      Ideal.map ((correspondenceRightExteriorProjection f g h i z w v).stalkMap x).hom
        (IsLocalRing.maximalIdeal ((correspondenceIncidence g h i w v).presheaf.stalk
          (correspondenceRightExteriorProjection f g h i z w v x))))).toNat

/-- Generic stalk Artinianness certifies finite fibre length before natural truncation. -/
theorem length_correspondenceRightExteriorFiber_ne_top
    [IsLocallyNoetherian (correspondenceRightIntermediateSupportProduct f g h i z w v)]
    (x : genericPoints (correspondenceRightIntermediateSupportProduct f g h i z w v)) :
    Module.length
      ((correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk x.1)
      ((correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk x.1 ⧸
        Ideal.map ((correspondenceRightExteriorProjection f g h i z w v).stalkMap x.1).hom
          (IsLocalRing.maximalIdeal ((correspondenceIncidence g h i w v).presheaf.stalk
            (correspondenceRightExteriorProjection f g h i z w v x.1)))) ≠ ⊤ := by
  let := generic_stalk_artinian x
  exact Module.length_ne_top

/-- Native 02M1 for the actual right exterior and any original coefficient sheaf. -/
theorem sheafMultiplicity_correspondenceRightExterior_pullback
    [Flat (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g)]
    (F : (correspondenceIncidence g h i w v).Modules)
    (x : correspondenceRightIntermediateSupportProduct f g h i z w v) :
    sheafMultiplicity
      ((Scheme.Modules.pullback (correspondenceRightExteriorProjection f g h i z w v)).obj F) x =
        sheafMultiplicity F (correspondenceRightExteriorProjection f g h i z w v x) *
          (correspondenceRightExteriorFiberLength f g h i z w v x : ℤ) := by
  let π := correspondenceRightExteriorProjection f g h i z w v
  let : Flat π := by dsimp [π, correspondenceRightExteriorProjection]; infer_instance
  exact sheafMultiplicity_pullback π F x

/-- Full signed finite windows keep the same actual exterior fibre factor. -/
theorem sum_signed_sheafMultiplicity_correspondenceRightExterior_pullback
    [Flat (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g)]
    (F : ℕ → (correspondenceIncidence g h i w v).Modules) (J : Finset ℕ)
    (x : correspondenceRightIntermediateSupportProduct f g h i z w v) :
    ∑ n ∈ J, (-1 : ℤ) ^ n * sheafMultiplicity
      ((Scheme.Modules.pullback (correspondenceRightExteriorProjection f g h i z w v)).obj
        (F n)) x =
      (∑ n ∈ J, (-1 : ℤ) ^ n *
        sheafMultiplicity (F n) (correspondenceRightExteriorProjection f g h i z w v x)) *
          (correspondenceRightExteriorFiberLength f g h i z w v x : ℤ) := by
  simp only [sheafMultiplicity_correspondenceRightExterior_pullback, Finset.sum_mul, mul_assoc]

end Stacks.Chow
