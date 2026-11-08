/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteFibre
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Actual generic triple labels above a generic image-incidence point

Every point of the actual finite triple-to-image fibre above a generic point is itself a
triple generic point. Indeed a generalization has the same image by target genericity, and
the finite morphism's discrete fibre has no nontrivial specializations. Thus the preceding
whole-algebra maximal-fibre equivalence restricts to the literal original generic triple
labels, without a supplied genericity dictionary or a reduced replacement.

The proof uses the native discrete-fibre theorem for locally quasi-finite morphisms and the
native characterization of generic points by specializations. No integral-fibre provider or
new algebra model is required.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i) [IsSeparated h]
  (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)

local notation3 (prettyPrint := false) "L" => correspondenceLeftImageIncidence f g h i z w v
local notation3 (prettyPrint := false) "C" => correspondenceTripleIncidence f g h i z w v
local notation3 (prettyPrint := false) "k" => correspondenceTripleToLeftImageIncidence f g h i z w v

/-- Above an actual generic image point, all finite-fibre points are original triple generics. -/
theorem mem_genericPoints_correspondenceRemainingTripleFibre
    (x : L) (hx : x ∈ genericPoints L)
    (y : correspondenceRemainingTripleFibre f g h i z w v x) : y.1 ∈ genericPoints C := by
  have := isFinite_correspondenceTripleToLeftImageIncidence f g h i z w v hz hw
  apply (mem_genericPoints_iff_forall_specializes_eq y.1).mpr
  intro y' hy'
  have hmap : k y' ⤳ x := by
    simpa only [y.2] using hy'.map (k).continuous
  have hpoint : k y' = x :=
    (mem_genericPoints_iff_forall_specializes_eq x).mp hx _ hmap
  have : DiscreteTopology ((k) ⁻¹' {x}) :=
    isDiscrete_iff_discreteTopology.mp ((k).isDiscrete_preimage_singleton x)
  let u : (k) ⁻¹' {x} := ⟨y', hpoint⟩
  let v : (k) ⁻¹' {x} := ⟨y.1, y.2⟩
  have hspec : u ⤳ v := (subtype_specializes_iff ..).mpr hy'
  exact congrArg Subtype.val hspec.eq

/-- The whole maximal spectrum parametrizes the retained original generic triple fibre. -/
def correspondenceRemainingFiniteMaximalEquivGenericTriple
    (x : L) (hx : x ∈ genericPoints L) :
    MaximalSpectrum (correspondenceRemainingFiniteRing f g h i z w v x) ≃
      {y : genericPoints C // k y.1 = x} :=
  (correspondenceRemainingFiniteMaximalEquivTriple f g h i z w v x hz hw).trans
    { toFun := fun y => ⟨⟨y.1,
        mem_genericPoints_correspondenceRemainingTripleFibre f g h i z w v hz hw x hx y⟩, y.2⟩
      invFun := fun y => ⟨y.1.1, y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- This restriction does not replace the original fibre point by another generic label. -/
theorem correspondenceRemainingFiniteMaximalEquivGenericTriple_val
    (x : L) (hx : x ∈ genericPoints L)
    (p : MaximalSpectrum (correspondenceRemainingFiniteRing f g h i z w v x)) :
    (correspondenceRemainingFiniteMaximalEquivGenericTriple f g h i z w v hz hw x hx p).1.1 =
      (correspondenceRemainingFiniteMaximalEquivTriple f g h i z w v x hz hw p).1 := rfl

/-- The actual original residue degree is unchanged on the retained generic labels. -/
theorem primeResidueDegree_correspondenceRemainingFiniteMaximalEquivGenericTriple
    (x : L) (hx : x ∈ genericPoints L)
    (p : MaximalSpectrum (correspondenceRemainingFiniteRing f g h i z w v x)) :
    letI := correspondenceRemainingFiniteAlgebra f g h i z w v x
    Stacks.Length.primeResidueDegree
      (algebraMap (correspondenceRemainingImageStalk f g h i z w v x)
        (correspondenceRemainingFiniteRing f g h i z w v x))
      (p.asIdeal.comap (algebraMap (correspondenceRemainingImageStalk f g h i z w v x)
        (correspondenceRemainingFiniteRing f g h i z w v x))) p.asIdeal =
      (k).residueDegree
        (correspondenceRemainingFiniteMaximalEquivGenericTriple f g h i z w v hz hw x hx p).1.1 :=
  primeResidueDegree_correspondenceRemainingFiniteMaximalEquivTriple f g h i z w v x hz hw p

end Stacks.Chow
