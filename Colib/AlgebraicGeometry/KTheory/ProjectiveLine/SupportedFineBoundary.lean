/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.SupportedOpenComparison
public import Colib.AlgebraicGeometry.KTheory.PerfectQcqsBoundaryTransport
public import Colib.Util.References

/-! # Fine connective boundary for the supported projective-line summands -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

variable (X : Scheme.{u}) (U : X.Opens)

local notation "P" => projectiveSpaceOver 1 X
local notation "π" => (P ↘ X)
local notation "Uₚ" => Functor.obj
  (TopologicalSpace.Opens.map (PresheafedSpace.Hom.base
    (LocallyRingedSpace.Hom.toHom (Scheme.Hom.toLRSHom π)))) U
local notation "j" => Scheme.Opens.ι Uₚ

variable [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U.toScheme]

local instance p1SupportedFineBoundaryProper : IsProper π := isProper_projectiveSpaceOver 1 X
local instance supportedFineBoundaryAmbientCompact : CompactSpace (projectiveSpaceOver 1 X) :=
  QuasiCompact.compactSpace_of_compactSpace π
local instance supportedFineBoundaryAmbientQS : QuasiSeparatedSpace (projectiveSpaceOver 1 X) :=
  quasiSeparatedSpace_of_quasiSeparated π
local instance supportedFineBoundaryOpenCompact : CompactSpace (Scheme.Opens.toScheme Uₚ) :=
  QuasiCompact.compactSpace_of_compactSpace ((π) ∣_ U)

/-- The actual supported first summand is natural for the fine localization boundary. -/
theorem projectiveLineSupportedFirstSummand_fineConnecting (n : ℕ) :
    (KMap (projectiveLineSupportedFirstSummand_exact X U) n).comp
      (perfectQcqsConnectingHom U.ι n) =
    (perfectQcqsConnectingHom (X := P) (U := Scheme.Opens.toScheme Uₚ) j n).comp
      (KMap (projectiveLineOpenFirstSummand_exact X U) (n + 1)) :=
  perfectQcqsConnectingHom_natural_of_relative
    (Y := P) (V := Scheme.Opens.toScheme Uₚ) U.ι j n _ _ _
    (projectiveLineSupportedFirstSummand_connecting X U n)
    (perfectOpenKRestrict_natural U.ι j (projectiveLineFirstSummand_coarseExact X U)
      (projectiveLineOpenFirstSummand_exact X U) (n + 1)
      (projectiveLineFirstSummand_restrictIso X U)).symm

/-- The actual supported twisted summand is natural for the fine localization boundary. -/
theorem projectiveLineSupportedSecondSummand_fineConnecting (n : ℕ) :
    (KMap (projectiveLineSupportedSecondSummand_exact X U) n).comp
      (perfectQcqsConnectingHom U.ι n) =
    (perfectQcqsConnectingHom (X := P) (U := Scheme.Opens.toScheme Uₚ) j n).comp
      (KMap (projectiveLineOpenSecondSummand_exact X U) (n + 1)) :=
  perfectQcqsConnectingHom_natural_of_relative
    (Y := P) (V := Scheme.Opens.toScheme Uₚ) U.ι j n _ _ _
    (projectiveLineSupportedSecondSummand_connecting X U n)
    (perfectOpenKRestrict_natural U.ι j (projectiveLineSecondSummand_coarseExact X U)
      (projectiveLineOpenSecondSummand_exact X U) (n + 1)
      (projectiveLineSecondSummand_restrictIso X U)).symm

/-- The two-summand map is natural for the canonical fine localization boundary. -/
@[colib_tag "COL-1292"]
theorem projectiveLineSupportedKMap_connecting (n : ℕ) :
    (perfectQcqsConnectingHom (X := P) (U := Scheme.Opens.toScheme Uₚ) j n).comp
      (projectiveLineOpenKMap X U (n + 1)) =
    (projectiveLineSupportedKMap X U n).comp
      ((perfectQcqsConnectingHom U.ι n).prodMap (perfectQcqsConnectingHom U.ι n)) := by
  refine MonoidHom.ext fun a => ?_
  change perfectQcqsConnectingHom (X := P) (U := Scheme.Opens.toScheme Uₚ) j n
      (projectiveLineOpenKMap X U (n + 1) (a.1, a.2)) =
    KMap (projectiveLineSupportedFirstSummand_exact X U) n
      (perfectQcqsConnectingHom U.ι n a.1) *
    KMap (projectiveLineSupportedSecondSummand_exact X U) n
      (perfectQcqsConnectingHom U.ι n a.2)
  rw [projectiveLineOpenKMap_apply, map_mul]
  exact congrArg₂ (· * ·)
    (DFunLike.congr_fun (projectiveLineSupportedFirstSummand_fineConnecting X U n) a.1).symm
    (DFunLike.congr_fun (projectiveLineSupportedSecondSummand_fineConnecting X U n) a.2).symm

end AlgebraicGeometry.Scheme
