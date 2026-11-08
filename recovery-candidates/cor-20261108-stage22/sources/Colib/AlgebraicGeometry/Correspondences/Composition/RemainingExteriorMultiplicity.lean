/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleAmbient
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.CoherentSheafCycle
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.Support
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Basic

/-!
# Multiplicity on the full first-stage exterior product

The actual projection from the whole first-stage incidence times the third
support is flat whenever that third support is flat over the base. Over any
field this hypothesis is automatic, including imperfect fields. Every exterior
generic label maps to an original generic label; this map need not be injective.

Native Stacks 02M1 gives the coefficient of every pulled-back module, with the
full closed-fibre length retained. Inseparable or non-geometrically reduced
products can have fibre length greater than one. The signed family formula
preserves this factor and every higher-degree sign. It does not replace the
first-stage Tor family by the structure sheaf, or assume that the actual first
Tor modules have already been identified with these pullbacks.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The actual exterior projection, without reducing the incidence or the product. -/
abbrev correspondenceLeftExteriorProjection :
    correspondenceLeftIntermediateSupportProduct f g h i z w v ⟶
      correspondenceIncidence f g h z w :=
  pullback.fst _ _

/-- The actual full exterior projection is flat by base change. The displayed
hypothesis is automatic for every third support over an arbitrary field. -/
instance flat_correspondenceLeftExteriorProjection
    [Flat (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)] :
    Flat (correspondenceLeftExteriorProjection f g h i z w v) := by
  dsimp only [correspondenceLeftExteriorProjection]
  infer_instance

/-- Every split exterior generic label retains its original first-stage generic label.
No injectivity or geometric reducedness is asserted. -/
def correspondenceLeftExteriorGenericLabel
    [Flat (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)]
    (x : genericPoints (correspondenceLeftIntermediateSupportProduct f g h i z w v)) :
    genericPoints (correspondenceIncidence f g h z w) :=
  ⟨correspondenceLeftExteriorProjection f g h i z w v x.1,
    (correspondenceLeftExteriorProjection f g h i z w v).mem_genericPoints_of_flat x.2⟩

/-- The full closed-fibre length at an exterior label. It is not replaced by one. -/
def correspondenceLeftExteriorFiberLength
    (x : correspondenceLeftIntermediateSupportProduct f g h i z w v) : ℕ :=
  (Module.length
    ((correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk x)
    ((correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk x ⧸
      Ideal.map ((correspondenceLeftExteriorProjection f g h i z w v).stalkMap x).hom
        (IsLocalRing.maximalIdeal ((correspondenceIncidence f g h z w).presheaf.stalk
          (correspondenceLeftExteriorProjection f g h i z w v x))))).toNat

/-- The actual closed-fibre length is finite at each exterior generic label. -/
theorem length_correspondenceLeftExteriorFiber_ne_top
    [IsLocallyNoetherian (correspondenceLeftIntermediateSupportProduct f g h i z w v)]
    (x : genericPoints (correspondenceLeftIntermediateSupportProduct f g h i z w v)) :
    Module.length
      ((correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk x.1)
      ((correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk x.1 ⧸
        Ideal.map ((correspondenceLeftExteriorProjection f g h i z w v).stalkMap x.1).hom
          (IsLocalRing.maximalIdeal ((correspondenceIncidence f g h z w).presheaf.stalk
            (correspondenceLeftExteriorProjection f g h i z w v x.1)))) ≠ ⊤ := by
  let := generic_stalk_artinian x
  exact Module.length_ne_top

/-- Native flat-local multiplicity for the actual full exterior projection.
The fibre multiplicity accounts for nonreduced tensor products over arbitrary fields. -/
theorem sheafMultiplicity_correspondenceLeftExterior_pullback
    [Flat (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)]
    (F : (correspondenceIncidence f g h z w).Modules)
    (x : correspondenceLeftIntermediateSupportProduct f g h i z w v) :
    sheafMultiplicity
      ((Scheme.Modules.pullback (correspondenceLeftExteriorProjection f g h i z w v)).obj F) x =
        sheafMultiplicity F (correspondenceLeftExteriorProjection f g h i z w v x) *
          (correspondenceLeftExteriorFiberLength f g h i z w v x : ℤ) :=
  sheafMultiplicity_pullback (correspondenceLeftExteriorProjection f g h i z w v) F x

/-- Each coefficient module is pulled back before the signed sum is taken.
All original higher-degree signs and the full exterior fibre multiplicity remain. -/
theorem sum_signed_sheafMultiplicity_correspondenceLeftExterior_pullback
    [Flat (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)]
    (F : ℕ → (correspondenceIncidence f g h z w).Modules) (s : Finset ℕ)
    (x : correspondenceLeftIntermediateSupportProduct f g h i z w v) :
    ∑ n ∈ s, (-1 : ℤ) ^ n * sheafMultiplicity
      ((Scheme.Modules.pullback (correspondenceLeftExteriorProjection f g h i z w v)).obj
        (F n)) x =
      (∑ n ∈ s, (-1 : ℤ) ^ n *
        sheafMultiplicity (F n) (correspondenceLeftExteriorProjection f g h i z w v x)) *
          (correspondenceLeftExteriorFiberLength f g h i z w v x : ℤ) := by
  simp only [sheafMultiplicity_correspondenceLeftExterior_pullback, Finset.sum_mul, mul_assoc]

end Stacks.Chow
