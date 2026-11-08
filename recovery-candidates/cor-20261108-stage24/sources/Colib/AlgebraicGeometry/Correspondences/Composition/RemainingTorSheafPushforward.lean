/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingImage
public import StacksFrontier.AlgebraicGeometry.Intersection.ProjectionFormulaFlat.AffineSupportTor
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.TorSheafIso
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeLocality.GlobalSectionsAffineCase
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCoherentImage.Basic
public import StacksFrontier.Topology.OpensMapFinal

/-!
# Remaining-diagonal Tor and the actual finite intermediate image

Write `A = (X × Y × Z) × (Z × W)`, `B = (X × Z) × (Z × W)`, and let
`p : A → B` forget `Y`. The full original pair incidence times the third
support is `J`, with closed inclusion `j : J → A`. Its full intermediate
image exterior is `I`, with finite map `q : J → I` and closed inclusion
`r : I → B`. The actual equality is `j ≫ p = q ≫ r`.

For a quasi-coherent module `F` on `J`, and the pushed structure module `G`
of the actual remaining diagonal in `B`, this file constructs

`p_* Tor_A(j_* F, O_remaining diagonal in A) ≅ Tor_B(r_* q_* F, G)`.

Both Tor sheaves are further computed from the native complex
`F ⊗ᴸ Lj* Lp* G` on the original full `J`. Thus the right-hand Tor sheaf
is `r_* q_* H^{-n}` of that complex. This gives an actual finite direct
image to which the residue-degree homology-length supplier can be applied
locally. No flatness of `q`, image reduction, or invented scalar action is used.

Flatness, quasi-compactness and quasi-separatedness of `p` are proved from
those of `Y → S`. The finite restriction follows from the original finite
correspondences and separation of `Z → S`; `p` need not be proper.

This is a genuine sheaf-level supplier. It does not identify the first-stage
coefficient module with an alternating Tor family, prove generic-label
Euler dévissage, or claim the weighted remaining-cycle identity.

## References

* Stacks 0B11 (the displayed comparison in the proof of 0B10): reused via
  `pushforwardTorSheafIsoOfIsAffineHom`, with verified ambient hypotheses.
* Stacks 02KG, assertion 3: ordinary affine base change identifies the two
  actual remaining diagonal structure modules. No flatness is needed for
  this ordinary structure-module base-change identification.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.TorFormula
open Stacks.Intersection.ProjectionFormula
open scoped BigOperators

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)

/-- The full remaining diagonal structure module in the target ambient. -/
abbrev correspondenceRemainingDiagonalModule : (correspondenceIntersectionAmbient f h i).Modules :=
  (Scheme.Modules.pushforward (correspondenceTripleInclusion f h i)).obj
    (SheafOfModules.unit (correspondenceTripleProduct f h i).ringCatSheaf)

/-- The full remaining diagonal structure module in the original first-diagonal ambient. -/
abbrev correspondenceOriginalRemainingDiagonalModule :
    (correspondenceFirstDiagonal f g h i).Modules :=
  (Scheme.Modules.pushforward (correspondenceSecondDiagonalInclusion f g h i)).obj
    (SheafOfModules.unit (correspondenceFourfoldProduct f g h i).ringCatSheaf)

/-- Quasi-coherence of the actual target diagonal module follows from its affine inclusion. -/
theorem isQuasicoherent_correspondenceRemainingDiagonalModule [IsSeparated h] :
    (correspondenceRemainingDiagonalModule f h i).IsQuasicoherent :=
  AlgebraicGeometry.ClosedImmersionCoherentImage.isQuasicoherent_pushforward_unit
    (correspondenceTripleInclusion f h i)

/-- Native affine base change identifies the actual remaining diagonal modules,
including their scheme structures, rather than just their set-theoretic supports. -/
def correspondenceRemainingDiagonalPullbackIso [IsSeparated h] :
    (Scheme.Modules.pullback (correspondenceRemainingProjection f g h i)).obj
        (correspondenceRemainingDiagonalModule f h i) ≅
      correspondenceOriginalRemainingDiagonalModule f g h i := by
  let a := correspondenceFourfoldRemainingProjection f g h i
  have : (SheafOfModules.pushforward a.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward a).IsRightAdjoint
  have : (TopologicalSpace.Opens.map a.base).Final := Stacks.Topology.final_opensMap _
  exact Stacks.AlgebraicGeometry.AffineBaseChangeLocality.baseChangeIso
      a (correspondenceSecondDiagonalInclusion f g h i)
      (correspondenceTripleInclusion f h i) (correspondenceRemainingProjection f g h i)
      (correspondenceRemainingDiagonal_isPullback f g h i) inferInstance
      (SheafOfModules.unit (correspondenceTripleProduct f h i).ringCatSheaf)
      (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit _) ≪≫
    (Scheme.Modules.pushforward (correspondenceSecondDiagonalInclusion f g h i)).mapIso
      (asIso (SheafOfModules.pullbackObjUnitToUnit a.toRingCatSheafHom))

variable (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The actual coefficient module pushed through the full finite image. -/
abbrev correspondenceRemainingImageModule
    (F : (correspondenceLeftIntermediateSupportProduct f g h i z w v).Modules) :
    (correspondenceIntersectionAmbient f h i).Modules :=
  (Scheme.Modules.pushforward (correspondenceLeftImageProductInclusion f g h i z w v)).obj
    ((Scheme.Modules.pushforward (correspondenceLeftIntermediateImageMap f g h i z w v)).obj F)

/-- The direct image along the ambient restriction is the direct image through
its actual finite image factorization. -/
def correspondenceRemainingCoefficientPushforwardIso
    (F : (correspondenceLeftIntermediateSupportProduct f g h i z w v).Modules) :
    (Scheme.Modules.pushforward (correspondenceRemainingProjection f g h i)).obj
        ((Scheme.Modules.pushforward
          (correspondenceLeftIntermediateSupportInclusion f g h i z w v)).obj F) ≅
      correspondenceRemainingImageModule f g h i z w v F :=
  (Scheme.Modules.pushforwardComp
      (correspondenceLeftIntermediateSupportInclusion f g h i z w v)
      (correspondenceRemainingProjection f g h i)).app F ≪≫
    (Scheme.Modules.pushforwardCongr
      ((correspondenceRemainingSupportMap_eq f g h i z w v).trans
        (correspondenceLeftIntermediateImageMap_inclusion f g h i z w v).symm)).app F ≪≫
    ((Scheme.Modules.pushforwardComp
      (correspondenceLeftIntermediateImageMap f g h i z w v)
      (correspondenceLeftImageProductInclusion f g h i z w v)).app F).symm

section FlatAmbient

variable [Flat g] [QuasiCompact g] [QuasiSeparated g] [IsSeparated h]
  (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)

/-- The native affine-support projection formula on the actual geometric diagram.
The left second argument is the original full remaining diagonal structure module. -/
def correspondenceRemainingTorSheafPushforwardIso
    (F : (correspondenceLeftIntermediateSupportProduct f g h i z w v).Modules)
    (hF : F.IsQuasicoherent) (n : ℕ) :
    (Scheme.Modules.pushforward (correspondenceRemainingProjection f g h i)).obj
      (torSheaf (correspondenceFirstDiagonal f g h i)
        ((Scheme.Modules.pushforward
          (correspondenceLeftIntermediateSupportInclusion f g h i z w v)).obj F)
        (correspondenceOriginalRemainingDiagonalModule f g h i) n) ≅
      torSheaf (correspondenceIntersectionAmbient f h i)
        (correspondenceRemainingImageModule f g h i z w v F)
        (correspondenceRemainingDiagonalModule f h i) n := by
  let j := correspondenceLeftIntermediateSupportInclusion f g h i z w v
  let p := correspondenceRemainingProjection f g h i
  let G := correspondenceRemainingDiagonalModule f h i
  let : IsFinite (correspondenceRemainingSupportMap f g h i z w v) :=
    isFinite_correspondenceRemainingSupportMap f g h i z w v hz hw
  have : IsFinite (j ≫ p) := by
    simpa only [j, p, correspondenceRemainingSupportMap_eq] using
      (inferInstance : IsFinite (correspondenceRemainingSupportMap f g h i z w v))
  let e := (correspondenceRemainingDiagonalPullbackIso f g h i).symm
  let eTor : torSheaf (correspondenceFirstDiagonal f g h i)
      ((Scheme.Modules.pushforward j).obj F)
      (correspondenceOriginalRemainingDiagonalModule f g h i) n ≅
    torSheaf (correspondenceFirstDiagonal f g h i)
      ((Scheme.Modules.pushforward j).obj F) ((Scheme.Modules.pullback p).obj G) n :=
    (DerivedCategory.homologyFunctor (correspondenceFirstDiagonal f g h i).Modules
      (-(n : ℤ))).mapIso
      (((derivedTensor (correspondenceFirstDiagonal f g h i)).obj
        ((DerivedCategory.singleFunctor (correspondenceFirstDiagonal f g h i).Modules 0).obj
          ((Scheme.Modules.pushforward j).obj F))).mapIso
        ((DerivedCategory.singleFunctor (correspondenceFirstDiagonal f g h i).Modules 0).mapIso e))
  exact (Scheme.Modules.pushforward p).mapIso eTor ≪≫
    pushforwardTorSheafIsoOfIsAffineHom p j F hF G
      (isQuasicoherent_correspondenceRemainingDiagonalModule f h i) n ≪≫
    torSheafMapIso (correspondenceRemainingCoefficientPushforwardIso f g h i z w v F) G n

/-- The actual homology module on the original entire first-stage exterior,
used by both sides of the native affine-support projection formula. -/
abbrev correspondenceRemainingHomology
    (F : (correspondenceLeftIntermediateSupportProduct f g h i z w v).Modules) (n : ℕ) :
    (correspondenceLeftIntermediateSupportProduct f g h i z w v).Modules :=
  (DerivedCategory.homologyFunctor
    (correspondenceLeftIntermediateSupportProduct f g h i z w v).Modules (-(n : ℤ))).obj
      (affineSupportTensor (correspondenceRemainingProjection f g h i)
        (correspondenceLeftIntermediateSupportInclusion f g h i z w v) F
        (correspondenceRemainingDiagonalModule f h i))

/-- On the target ambient, remaining Tor is the finite direct image of the actual
remaining homology on the original full exterior. No finite-map flatness is assumed. -/
def correspondenceRemainingTorSheafFiniteImageIso
    (F : (correspondenceLeftIntermediateSupportProduct f g h i z w v).Modules)
    (hF : F.IsQuasicoherent) (n : ℕ) :
    torSheaf (correspondenceIntersectionAmbient f h i)
        (correspondenceRemainingImageModule f g h i z w v F)
        (correspondenceRemainingDiagonalModule f h i) n ≅
      correspondenceRemainingImageModule f g h i z w v
        (correspondenceRemainingHomology f g h i z w v F n) := by
  let j := correspondenceLeftIntermediateSupportInclusion f g h i z w v
  let p := correspondenceRemainingProjection f g h i
  let q := correspondenceLeftIntermediateImageMap f g h i z w v
  let r := correspondenceLeftImageProductInclusion f g h i z w v
  let G := correspondenceRemainingDiagonalModule f h i
  let : IsFinite (correspondenceRemainingSupportMap f g h i z w v) :=
    isFinite_correspondenceRemainingSupportMap f g h i z w v hz hw
  have : IsFinite (j ≫ p) := by
    simpa only [j, p, correspondenceRemainingSupportMap_eq] using
      (inferInstance : IsFinite (correspondenceRemainingSupportMap f g h i z w v))
  exact torSheafMapIso
      (correspondenceRemainingCoefficientPushforwardIso f g h i z w v F).symm G n ≪≫
    torSheafPushforwardCompIso p j F hF G
      (isQuasicoherent_correspondenceRemainingDiagonalModule f h i) n ≪≫
    (Scheme.Modules.pushforwardCongr
      ((correspondenceRemainingSupportMap_eq f g h i z w v).trans
        (correspondenceLeftIntermediateImageMap_inclusion f g h i z w v).symm)).app _ ≪≫
    ((Scheme.Modules.pushforwardComp q r).app _).symm

/-- Every coefficient of the target remaining Tor sheaf is the multiplicity of
that concrete finite direct image. This is not yet a generic-label devissage. -/
theorem sheafMultiplicity_correspondenceRemainingTor_eq
    (F : (correspondenceLeftIntermediateSupportProduct f g h i z w v).Modules)
    (hF : F.IsQuasicoherent) (n : ℕ) (x : correspondenceIntersectionAmbient f h i) :
    sheafMultiplicity
      (torSheaf (correspondenceIntersectionAmbient f h i)
        (correspondenceRemainingImageModule f g h i z w v F)
        (correspondenceRemainingDiagonalModule f h i) n) x =
      sheafMultiplicity
        (correspondenceRemainingImageModule f g h i z w v
          (correspondenceRemainingHomology f g h i z w v F n)) x :=
  sheafMultiplicity_eq_of_iso
    (correspondenceRemainingTorSheafFiniteImageIso f g h i z w v hz hw F hF n) x

end FlatAmbient

end Stacks.Chow
