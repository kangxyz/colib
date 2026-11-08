/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleAmbient
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor

/-!
# The actual common sixfold stalk modules

The coefficient is the full exterior product of the three original integral
supports, and the second input is the actual fourfold product. Both local rings
are restricted along the actual maps to the same sixfold local ring. The only
transport is between proved-equal images of one actual triple-incidence point.
The incidence itself, the exterior product, and the diagonal cuts are not reduced.

These are concrete inputs to native categorical Tor. No comparison with either
iterated correspondence pairing or a chosen Koszul complex is assumed or proved
here. In particular, this file does not declare finite lengths or an Euler sum.

Adapted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
Correspondences/Composition/Associativity/IncidenceTor.lean,
Git blob 4c2fa80bcc39e51a964cc7a25d3b1daa17ddda96. The generic module constructors
are Mathlib's restrictScalars and Tor, not a replacement tensor model.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The literal map from full triple incidence to the original three-support product. -/
abbrev correspondenceTripleIncidenceToTripleSupport :
    correspondenceTripleIncidence f g h i z w v ⟶
      correspondenceTripleSupportProduct f g h i z w v :=
  correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v ≫
    correspondenceLeftIntermediateToTripleSupport f g h i z w v

/-- The combined diagonal is the original composition of its two closed inclusions. -/
abbrev correspondenceFourfoldDiagonalInclusion :
    correspondenceFourfoldProduct f g h i ⟶ correspondenceSixfoldAmbient f g h i :=
  correspondenceSecondDiagonalInclusion f g h i ≫ correspondenceFirstDiagonalInclusion f g h i

instance isClosedImmersion_correspondenceFourfoldDiagonalInclusion
    [IsSeparated g] [IsSeparated h] :
    IsClosedImmersion (correspondenceFourfoldDiagonalInclusion f g h i) := by
  dsimp only [correspondenceFourfoldDiagonalInclusion]
  infer_instance

/-- The two actual images of a triple-incidence point in the sixfold ambient agree. -/
theorem correspondenceTripleIncidence_ambient_point_eq
    (t : correspondenceTripleIncidence f g h i z w v) :
    correspondenceFourfoldDiagonalInclusion f g h i
        (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v t) =
      correspondenceTripleSupportProductInclusion f g h i z w v
        (correspondenceTripleIncidenceToTripleSupport f g h i z w v t) := by
  simpa only [Scheme.Hom.comp_apply] using
    congrArg (fun m : correspondenceTripleIncidence f g h i z w v ⟶
        correspondenceSixfoldAmbient f g h i => m t)
      (correspondenceTripleIncidence_sixfold_isPullback f g h i z w v).w

/-- The local ring of the actual sixfold ambient at a full triple-incidence point. -/
abbrev correspondenceTripleIncidenceAmbientStalk
    (t : correspondenceTripleIncidence f g h i z w v) :=
  (correspondenceSixfoldAmbient f g h i).presheaf.stalk
    (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v t)

/-- The full exterior-support local ring with its actual, transported sixfold action. -/
abbrev correspondenceTripleIncidenceSupportStalkModule
    (t : correspondenceTripleIncidence f g h i z w v) :
    ModuleCat (correspondenceTripleIncidenceAmbientStalk f g h i z w v t) :=
  (ModuleCat.restrictScalars
    (((correspondenceSixfoldAmbient f g h i).presheaf.stalkCongr
      (.of_eq (correspondenceTripleIncidence_ambient_point_eq f g h i z w v t))).hom ≫
        (correspondenceTripleSupportProductInclusion f g h i z w v).stalkMap
          (correspondenceTripleIncidenceToTripleSupport f g h i z w v t)).hom).obj
    (ModuleCat.of
      ((correspondenceTripleSupportProduct f g h i z w v).presheaf.stalk
        (correspondenceTripleIncidenceToTripleSupport f g h i z w v t))
      ((correspondenceTripleSupportProduct f g h i z w v).presheaf.stalk
        (correspondenceTripleIncidenceToTripleSupport f g h i z w v t)))

/-- The full fourfold-product local ring with the original combined-diagonal action. -/
abbrev correspondenceTripleIncidenceFourfoldStalkModule
    (t : correspondenceTripleIncidence f g h i z w v) :
    ModuleCat (correspondenceTripleIncidenceAmbientStalk f g h i z w v t) :=
  (ModuleCat.restrictScalars
    ((correspondenceFourfoldDiagonalInclusion f g h i).stalkMap
      (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v t)).hom).obj
    (ModuleCat.of
      ((correspondenceFourfoldProduct f g h i).presheaf.stalk
        (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v t))
      ((correspondenceFourfoldProduct f g h i).presheaf.stalk
        (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v t)))

/-- Native Tor of the actual exterior-support and combined-diagonal stalk modules. -/
abbrev correspondenceTripleIncidenceTor
    (t : correspondenceTripleIncidence f g h i z w v) (n : ℕ) :
    ModuleCat (correspondenceTripleIncidenceAmbientStalk f g h i z w v t) :=
  ((Tor (ModuleCat (correspondenceTripleIncidenceAmbientStalk f g h i z w v t)) n).obj
    (correspondenceTripleIncidenceSupportStalkModule f g h i z w v t)).obj
      (correspondenceTripleIncidenceFourfoldStalkModule f g h i z w v t)

/-- The full common-incidence local ring, with the actual sixfold stalk action. -/
abbrev correspondenceTripleIncidenceStalkModule
    (t : correspondenceTripleIncidence f g h i z w v) :
    ModuleCat (correspondenceTripleIncidenceAmbientStalk f g h i z w v t) :=
  (ModuleCat.restrictScalars
    ((correspondenceTripleIncidenceSixfoldInclusion f g h i z w v).stalkMap t).hom).obj
    (ModuleCat.of ((correspondenceTripleIncidence f g h i z w v).presheaf.stalk t)
      ((correspondenceTripleIncidence f g h i z w v).presheaf.stalk t))

end Stacks.Chow
