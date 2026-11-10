/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectApproximation
public import Colib.AlgebraicGeometry.Modules.PerfectOpenWeak
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.CoarseJoint

/-!
# Bounded-flat perfect complexes with open-detected weak equivalences

Objects and admissible bounded-flat quotients are unchanged. Weak equivalences are
precisely quasi-isomorphisms after the actual open restriction, with no support
condition on the objects. This is not ambient fine K-theory.

Adapted from Quillen `BoundedFlat/OpenComparison.lean:34-70` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.Fibration AlgebraicGeometry.RingedSpace

universe u
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Retain the actual bounded-flat category and test weak equivalences on the open. -/
@[colib_tag "COL-0386",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/OpenComparison.lean:34-36"
    "adaptation" "Original bounded-flat objects and actual open-restriction weak equivalences"]
def boundedAboveFlatPerfectOpenWaldhausen :
    Waldhausen.Structure (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory :=
  Structure.withInverseImageWeak
    ((boundedAboveFlatPerfectInclusion_isExact X.toRingedSpace).comp
      (perfectComplexesRestrictOpenImmersion_isExact j))

/-- The ordinary quasi-isomorphisms lie in the actual open-detected weak class. -/
def boundedAboveFlatPerfectOpenNested :
    NestedWeakEquivalences (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) :=
  Structure.inverseImageWeakNested
    ((boundedAboveFlatPerfectInclusion_isExact X.toRingedSpace).comp
      (perfectComplexesRestrictOpenImmersion_isExact j))

/-- Weakness is tested on the original restricted underlying chain map. -/
theorem boundedAboveFlatPerfectOpenWaldhausen_weq_iff
    {K L : (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory} (f : K ⟶ L) :
    (boundedAboveFlatPerfectOpenWaldhausen j).weq f ↔
      QuasiIso (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map f.hom) :=
  Iff.rfl

/-- The relative model keeps exactly the original admissible bounded-flat quotients. -/
theorem boundedAboveFlatPerfectOpenWaldhausen_cof_iff
    {K L : (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory} (f : K ⟶ L) :
    (boundedAboveFlatPerfectOpenWaldhausen j).cof f ↔
      ∃ (Q : CochainComplex (StrictlyPerfect.OXMod X.toRingedSpace) ℤ)
        (_hQ : boundedAboveFlatPerfectComplex X.toRingedSpace Q)
        (p : L.obj ⟶ Q) (h : f.hom ≫ p = 0),
        (ShortComplex.mk f.hom p h).ShortExact :=
  boundedAboveFlatPerfectWaldhausen_cof_iff X.toRingedSpace f

/-- The literal bounded-flat inclusion is exact for the actual relative weak structures. -/
theorem boundedAboveFlatPerfectOpenInclusion_isExact :
    IsExact (boundedAboveFlatPerfectOpenWaldhausen j).cof
      (boundedAboveFlatPerfectOpenWaldhausen j).weq
      (perfectOpenWeakWaldhausen j).cof (perfectOpenWeakWaldhausen j).weq
      (boundedAboveFlatPerfectInclusion X.toRingedSpace) where
  zero := (boundedAboveFlatPerfectInclusion_isExact X.toRingedSpace).zero
  cofibration := (boundedAboveFlatPerfectInclusion_isExact X.toRingedSpace).cofibration
  weak _ h := h
  pushout := (boundedAboveFlatPerfectInclusion_isExact X.toRingedSpace).pushout

/-- The relative source keeps the actual bounded-flat identity-cone joint cylinder. -/
def boundedAboveFlatPerfectOpenJointData :
    RowFactorization.JointData (boundedAboveFlatPerfectOpenNested j) :=
  boundedAboveFlatPerfectJointData X.toRingedSpace (boundedAboveFlatPerfectOpenNested j)

/-- Fine replacements prove relative approximation with only a compact ambient space. -/
theorem boundedAboveFlatPerfectOpenInclusion_approximation [CompactSpace X] :
    HasApproximationProperty (boundedAboveFlatPerfectOpenWaldhausen j)
      (perfectOpenWeakWaldhausen j) (boundedAboveFlatPerfectInclusion X.toRingedSpace) where
  reflects _ h := h
  lift f := by
    obtain ⟨M, i, p, hi, hp, hfac⟩ :=
      (boundedAboveFlatPerfectInclusion_approximation X.toRingedSpace).lift f
    exact ⟨M, i, p, hi, (perfectOpenNested j).le_weq p hp, hfac⟩

instance boundedAboveFlatPerfectOpenNested_twoOutOfThree :
    (boundedAboveFlatPerfectOpenNested j).coarse.weq.HasTwoOutOfThreeProperty := by
  let : (complexes (StrictlyPerfect.OXMod U.toRingedSpace)).weq.HasTwoOutOfThreeProperty := by
    change (HomologicalComplex.quasiIso (StrictlyPerfect.OXMod U.toRingedSpace)
      (ComplexShape.up ℤ)).HasTwoOutOfThreeProperty
    infer_instance
  let : (perfectComplexesWaldhausen U.toRingedSpace).weq.HasTwoOutOfThreeProperty :=
    CofibrationClosedSubcategory.twoOutOfThree _ _ _
  exact Structure.withInverseImageWeak_twoOutOfThree
    ((boundedAboveFlatPerfectInclusion_isExact X.toRingedSpace).comp
      (perfectComplexesRestrictOpenImmersion_isExact j))

end AlgebraicGeometry.Scheme.Modules
