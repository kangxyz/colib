/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleGenericSupport
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.TripleProductAssociativity

/-!
# The two actual diagonal orders have equal iterated Tor coefficients

All three inputs live in the unchanged actual sixfold local ring: the Y-diagonal
quotient, the full exterior-support module, and the Z-diagonal quotient. At an
original generic triple-incidence point their three supports meet only at the
closed point, by `TripleGenericSupport`. The original smooth factors make that
ring regular over any field, without perfection or connectedness assumptions.

Native Stacks 0B1L then equates both iterated Tor Euler sums. Native Tor symmetry
places the remaining diagonal in the first argument on each side, exactly as
required by coefficient Koszul homology. Every individual length is proved finite;
both homological indices are bounded by the actual local dimension. The signs are
literally `(-1)^(a+b)`, with no change of indexing or discarded higher degree.

This is a specialization of the public native local associativity theorem, not
an extraction or copy of its private spectral-sequence proof. It defines no new
cycle. It does not identify either sum with total-complex homology or claim that
the original correspondence brackets already equal these local coefficients.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped BigOperators

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- First impose the original Y diagonal, then the original Z diagonal, using native Tor. -/
abbrev correspondenceTripleIncidenceLeftIteratedTor
    (x : correspondenceTripleIncidence f g h i z w v) (a b : ℕ) :
    ModuleCat (correspondenceTripleIncidenceAmbientStalk f g h i z w v x) :=
  ((Tor (ModuleCat (correspondenceTripleIncidenceAmbientStalk f g h i z w v x)) a).obj
    (correspondenceTripleIncidenceSecondDiagonalQuotient f g h i z w v x)).obj
      (((Tor (ModuleCat (correspondenceTripleIncidenceAmbientStalk f g h i z w v x)) b).obj
        (correspondenceTripleIncidenceFirstDiagonalQuotient f g h i z w v x)).obj
          (correspondenceTripleIncidenceSupportStalkModule f g h i z w v x))

/-- First impose the original Z diagonal, then the original Y diagonal, on the same module. -/
abbrev correspondenceTripleIncidenceRightIteratedTor
    (x : correspondenceTripleIncidence f g h i z w v) (a b : ℕ) :
    ModuleCat (correspondenceTripleIncidenceAmbientStalk f g h i z w v x) :=
  ((Tor (ModuleCat (correspondenceTripleIncidenceAmbientStalk f g h i z w v x)) a).obj
    (correspondenceTripleIncidenceFirstDiagonalQuotient f g h i z w v x)).obj
      (((Tor (ModuleCat (correspondenceTripleIncidenceAmbientStalk f g h i z w v x)) b).obj
        (correspondenceTripleIncidenceSecondDiagonalQuotient f g h i z w v x)).obj
          (correspondenceTripleIncidenceSupportStalkModule f g h i z w v x))

/-- Every left-column Tor length is finite at an actual generic triple point. -/
theorem length_correspondenceTripleIncidenceLeftIteratedTor_ne_top
    [IsSeparated g] [IsSeparated h]
    [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]
    (x : genericPoints (correspondenceTripleIncidence f g h i z w v)) (a b : ℕ) :
    Module.length (correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1)
      (correspondenceTripleIncidenceLeftIteratedTor f g h i z w v x.1 a b) ≠ ⊤ := by
  let A := correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1
  let Y := correspondenceTripleIncidenceFirstDiagonalQuotient f g h i z w v x.1
  let Z := correspondenceTripleIncidenceSecondDiagonalQuotient f g h i z w v x.1
  let M := correspondenceTripleIncidenceSupportStalkModule f g h i z w v x.1
  let H := ((Tor (ModuleCat A) b).obj Y).obj M
  have : Module.Finite A M := finite_correspondenceTripleIncidenceSupportStalkModule
    f g h i z w v x.1
  have : Module.Finite A H := tor_finite_of_noetherian A Y M b
  have : Module.Finite A (((Tor (ModuleCat A) a).obj Z).obj H) :=
    tor_finite_of_noetherian A Z H a
  apply Module.length_ne_top_iff.mpr
  apply isFiniteLength_of_support_subset (R := A)
  intro q hq
  obtain ⟨hZ, hH⟩ := Stacks.Intersection.support_tor_subset_inter Z H a hq
  obtain ⟨hY, hM⟩ := Stacks.Intersection.support_tor_subset_inter Y M b hH
  exact support_correspondenceTripleIncidence_threeModules f g h i z w v x ⟨⟨hY, hM⟩, hZ⟩

/-- Every right-column Tor length is finite at the same original generic triple point. -/
theorem length_correspondenceTripleIncidenceRightIteratedTor_ne_top
    [IsSeparated g] [IsSeparated h]
    [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]
    (x : genericPoints (correspondenceTripleIncidence f g h i z w v)) (a b : ℕ) :
    Module.length (correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1)
      (correspondenceTripleIncidenceRightIteratedTor f g h i z w v x.1 a b) ≠ ⊤ := by
  let A := correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1
  let Y := correspondenceTripleIncidenceFirstDiagonalQuotient f g h i z w v x.1
  let Z := correspondenceTripleIncidenceSecondDiagonalQuotient f g h i z w v x.1
  let M := correspondenceTripleIncidenceSupportStalkModule f g h i z w v x.1
  let H := ((Tor (ModuleCat A) b).obj Z).obj M
  have : Module.Finite A M := finite_correspondenceTripleIncidenceSupportStalkModule
    f g h i z w v x.1
  have : Module.Finite A H := tor_finite_of_noetherian A Z M b
  have : Module.Finite A (((Tor (ModuleCat A) a).obj Y).obj H) :=
    tor_finite_of_noetherian A Y H a
  apply Module.length_ne_top_iff.mpr
  apply isFiniteLength_of_support_subset (R := A)
  intro q hq
  obtain ⟨hY, hH⟩ := Stacks.Intersection.support_tor_subset_inter Y H a hq
  obtain ⟨hZ, hM⟩ := Stacks.Intersection.support_tor_subset_inter Z M b hH
  exact support_correspondenceTripleIncidence_threeModules f g h i z w v x ⟨⟨hY, hM⟩, hZ⟩

section Field

variable (k : Type u) [Field k] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  (h : Z ⟶ Spec (.of k)) (i : W ⟶ Spec (.of k))
  [Smooth f] [Smooth g] [Smooth h] [Smooth i]
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- Either index exceeding the actual ambient dimension kills the left iterated module. -/
theorem isZero_correspondenceTripleIncidenceLeftIteratedTor_of_lt
    (x : correspondenceTripleIncidence f g h i z w v) (a b : ℕ)
    (hab : correspondenceTripleIncidenceTorDegreeBound k f g h i z w v x < a ∨
      correspondenceTripleIncidenceTorDegreeBound k f g h i z w v x < b) :
    IsZero (correspondenceTripleIncidenceLeftIteratedTor f g h i z w v x a b) := by
  have := isRegularLocalRing_correspondenceSixfoldAmbient_stalk k f g h i
    (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x)
  let A := correspondenceTripleIncidenceAmbientStalk f g h i z w v x
  let Y := correspondenceTripleIncidenceFirstDiagonalQuotient f g h i z w v x
  let Z := correspondenceTripleIncidenceSecondDiagonalQuotient f g h i z w v x
  let M := correspondenceTripleIncidenceSupportStalkModule f g h i z w v x
  have hd := (ringKrullDim_eq_correspondenceTripleIncidenceTorDegreeBound
    k f g h i z w v x).le
  rcases hab with ha | hb
  · exact AlgebraicGeometry.TorFormula.isZero_Tor_of_isRegularLocalRing Z _ _ a hd ha
  · exact ((Tor (ModuleCat A) a).obj Z).map_isZero
      (AlgebraicGeometry.TorFormula.isZero_Tor_of_isRegularLocalRing Y M _ b hd hb)

/-- The same actual dimension bounds both indices in the other diagonal order. -/
theorem isZero_correspondenceTripleIncidenceRightIteratedTor_of_lt
    (x : correspondenceTripleIncidence f g h i z w v) (a b : ℕ)
    (hab : correspondenceTripleIncidenceTorDegreeBound k f g h i z w v x < a ∨
      correspondenceTripleIncidenceTorDegreeBound k f g h i z w v x < b) :
    IsZero (correspondenceTripleIncidenceRightIteratedTor f g h i z w v x a b) := by
  have := isRegularLocalRing_correspondenceSixfoldAmbient_stalk k f g h i
    (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x)
  let A := correspondenceTripleIncidenceAmbientStalk f g h i z w v x
  let Y := correspondenceTripleIncidenceFirstDiagonalQuotient f g h i z w v x
  let Z := correspondenceTripleIncidenceSecondDiagonalQuotient f g h i z w v x
  let M := correspondenceTripleIncidenceSupportStalkModule f g h i z w v x
  have hd := (ringKrullDim_eq_correspondenceTripleIncidenceTorDegreeBound
    k f g h i z w v x).le
  rcases hab with ha | hb
  · exact AlgebraicGeometry.TorFormula.isZero_Tor_of_isRegularLocalRing Y _ _ a hd ha
  · exact ((Tor (ModuleCat A) a).obj Y).map_isZero
      (AlgebraicGeometry.TorFormula.isZero_Tor_of_isRegularLocalRing Z M _ b hd hb)

/-- Native local triple-Tor associativity for the two original diagonal orders on the
full exterior module, with the original generic triple-incidence label fixed. -/
@[stacks 0B1L "specialization of the public native regular-local triple-Tor Euler theorem to \
the actual Y diagonal, full exterior-support stalk, and Z diagonal in the original sixfold \
ambient; regularity, finite generation, dimension bound and generic support are proved"]
theorem finsum_signed_length_correspondenceTripleIncidence_iteratedTor_eq
    [IsSeparated g] [IsSeparated h]
    (x : genericPoints (correspondenceTripleIncidence f g h i z w v)) :
    (∑ᶠ ab : ℕ × ℕ, (-1 : ℤ) ^ (ab.1 + ab.2) *
      ((Module.length (correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1)
        (correspondenceTripleIncidenceLeftIteratedTor f g h i z w v x.1
          ab.1 ab.2)).toNat : ℤ)) =
    ∑ᶠ ab : ℕ × ℕ, (-1 : ℤ) ^ (ab.1 + ab.2) *
      ((Module.length (correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1)
        (correspondenceTripleIncidenceRightIteratedTor f g h i z w v x.1
          ab.1 ab.2)).toNat : ℤ) := by
  let A := correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1
  let Y := correspondenceTripleIncidenceFirstDiagonalQuotient f g h i z w v x.1
  let Z := correspondenceTripleIncidenceSecondDiagonalQuotient f g h i z w v x.1
  let M := correspondenceTripleIncidenceSupportStalkModule f g h i z w v x.1
  have : IsRegularLocalRing A := isRegularLocalRing_correspondenceSixfoldAmbient_stalk
    k f g h i (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x.1)
  have : IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i) :=
    LocallyOfFiniteType.isLocallyNoetherian (correspondenceSixfoldAmbientToField k f g h i)
  have : Module.Finite A M := finite_correspondenceTripleIncidenceSupportStalkModule
    f g h i z w v x.1
  have hassoc := Stacks.Intersection.finsum_alternating_length_tor_assoc_of_isRegularLocalRing
    A Y M Z (correspondenceTripleIncidenceTorDegreeBound k f g h i z w v x.1)
    (ringKrullDim_eq_correspondenceTripleIncidenceTorDegreeBound k f g h i z w v x.1).le
    (support_correspondenceTripleIncidence_threeModules f g h i z w v x)
  calc
    _ = ∑ᶠ ab : ℕ × ℕ, (-1 : ℤ) ^ (ab.1 + ab.2) *
        ((Module.length A (((Tor (ModuleCat A) ab.1).obj
          (((Tor (ModuleCat A) ab.2).obj Y).obj M)).obj Z)).toNat : ℤ) := by
      apply finsum_congr
      intro ab
      let e := (((Tor_iso_Tor' A ab.1) ≪≫ (torFlip_iso_Tor' A ab.1).symm).app Z).app
        (((Tor (ModuleCat A) ab.2).obj Y).obj M)
      exact congrArg (fun l : ℕ∞ => (-1 : ℤ) ^ (ab.1 + ab.2) * (l.toNat : ℤ))
        e.toLinearEquiv.length_eq
    _ = ∑ᶠ ab : ℕ × ℕ, (-1 : ℤ) ^ (ab.1 + ab.2) *
        ((Module.length A (((Tor (ModuleCat A) ab.1).obj Y).obj
          (((Tor (ModuleCat A) ab.2).obj M).obj Z))).toNat : ℤ) := hassoc.symm
    _ = _ := by
      apply finsum_congr
      intro ab
      let e := (((Tor_iso_Tor' A ab.2) ≪≫ (torFlip_iso_Tor' A ab.2).symm).app M).app Z
      exact congrArg (fun l : ℕ∞ => (-1 : ℤ) ^ (ab.1 + ab.2) * (l.toNat : ℤ))
        (((Tor (ModuleCat A) ab.1).obj Y).mapIso e).toLinearEquiv.length_eq

end Field

end Stacks.Chow
