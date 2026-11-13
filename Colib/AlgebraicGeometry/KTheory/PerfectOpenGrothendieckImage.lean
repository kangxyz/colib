/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectOpenKZeroImage
public import Colib.AlgebraicGeometry.KTheory.PerfectGrothendieckComparison
public import Colib.KTheory.Waldhausen.GrothendieckGroup.Image

/-!
# The original fine and relative-open algebraic restriction images

The accepted equality of the actual K-zero restriction images transports
through the genuine original Grothendieck comparisons. The resulting equality
is in the unchanged target group of perfect complexes on the open. This selected
file contains only that range equality and its original image witness helper.
The quotient equivalence is outside this selected scope.
-/
@[expose] public section

open AlgebraicGeometry.RingedSpace

open CategoryTheory.Waldhausen


noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Waldhausen.AlgebraicGrothendieck
universe u v
namespace AlgebraicGeometry.Scheme.Modules

private theorem original_map_mem_range {C D : Type u} [Category.{v} C] [Category.{v} D]
    (W : Structure C) (V : Structure D) (F : C ⥤ D)
    (hF : IsExact W.cof W.weq V.cof V.weq F) (y : Group V) :
    y ∈ (map W F hF).range ↔
      grothendieckKZeroEquivOfAsSmall V (Multiplicative.ofAdd y) ∈ (KMap hF 0).range := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨grothendieckKZeroEquivOfAsSmall W (Multiplicative.ofAdd a),
      grothendieckKZeroEquivOfAsSmall_natural W V F hF (Multiplicative.ofAdd a)⟩
  · rintro ⟨a, ha⟩
    refine ⟨((grothendieckKZeroEquivOfAsSmall W).symm a).toAdd, ?_⟩
    have hn := grothendieckKZeroEquivOfAsSmall_natural W V F hF
      ((grothendieckKZeroEquivOfAsSmall W).symm a)
    rw [MulEquiv.apply_symm_apply] at hn
    exact congrArg Multiplicative.toAdd
      ((grothendieckKZeroEquivOfAsSmall V).injective (hn.symm.trans ha))

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The actual relative-open and fine restriction images coincide in the original target group. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/OpenGrothendieckImage.lean:54"
  "adaptation" "Original actual ordinary raw-image quotient action"]
theorem range_perfectOpenGrothendieckRestrict :
    (map (perfectOpenWeakWaldhausen j) (perfectComplexesRestrictOpenImmersion j)
      (perfectOpenRestrict_isExact j)).range =
    (map (perfectComplexesWaldhausen X.toRingedSpace) (perfectComplexesRestrictOpenImmersion j)
      (perfectComplexesRestrictOpenImmersion_isExact j)).range := by
  ext y
  rw [original_map_mem_range (perfectOpenWeakWaldhausen j) (perfectComplexesWaldhausen
    U.toRingedSpace)
    (perfectComplexesRestrictOpenImmersion j) (perfectOpenRestrict_isExact j),
    original_map_mem_range (perfectComplexesWaldhausen X.toRingedSpace)
      (perfectComplexesWaldhausen U.toRingedSpace)
      (perfectComplexesRestrictOpenImmersion j) (perfectComplexesRestrictOpenImmersion_isExact j)]
  change grothendieckKZeroEquivOfAsSmall (perfectComplexesWaldhausen U.toRingedSpace)
    (Multiplicative.ofAdd y) ∈
      (perfectOpenKRestrict j 0).range ↔
    grothendieckKZeroEquivOfAsSmall (perfectComplexesWaldhausen U.toRingedSpace)
      (Multiplicative.ofAdd y) ∈
      (KMap (perfectComplexesRestrictOpenImmersion_isExact j) 0).range
  rw [range_perfectOpenKRestrict_zero]


end AlgebraicGeometry.Scheme.Modules
