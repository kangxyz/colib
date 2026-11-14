/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Group.MulExactProduct
public import Colib.AlgebraicGeometry.KTheory.PerfectQcqsConnectiveLocalization
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.OpenBaseChangeKMap
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.SupportedFineBoundary
public import Colib.Util.References

/-! # The projective-line formula with support from the localization diagram

The proof uses the actual fine connective localization rows, including their
degree-zero restriction maps. The actual restriction, forgetting-support, and
connecting squares give the result by the group five lemma.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

variable (X : Scheme.{u}) (U : X.Opens) [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace U.toScheme]

local notation "P" => projectiveSpaceOver 1 X
local notation "π" => (P ↘ X)
local notation "V" => Functor.obj
  (TopologicalSpace.Opens.map (PresheafedSpace.Hom.base
    (LocallyRingedSpace.Hom.toHom (Scheme.Hom.toLRSHom π)))) U
local notation "Y" => Scheme.Opens.toScheme V
local notation "j" => Scheme.Opens.ι V

local instance p1SupportedFiveLemmaProper : IsProper π := isProper_projectiveSpaceOver 1 X
local instance supportedFiveLemmaAmbientCompact : CompactSpace (projectiveSpaceOver 1 X) :=
  QuasiCompact.compactSpace_of_compactSpace π
local instance supportedFiveLemmaAmbientQS : QuasiSeparatedSpace (projectiveSpaceOver 1 X) :=
  quasiSeparatedSpace_of_quasiSeparated π
local instance supportedFiveLemmaOpenCompact : CompactSpace (Scheme.Opens.toScheme V) :=
  QuasiCompact.compactSpace_of_compactSpace ((π) ∣_ U)

local notation:max "r[" n "]" =>
  KMap (perfectComplexesRestrictOpenImmersion_isExact (Scheme.Opens.ι U)) n
local notation:max "rP[" n "]" => KMap (perfectComplexesRestrictOpenImmersion_isExact j) n
local notation:max "Φ[" n "]" => projectiveLineKMap X n
local notation:max "ΦU[" n "]" => projectiveLineOpenKMap X U n

/-- The localization diagram and the ordinary projective-line formula imply the
supported formula in the indicated connective degree. -/
theorem projectiveLineSupportedKMap_bijective_of_localizationSquares (n : ℕ)
    (hn : (rP[n]).comp (Φ[n]) = (ΦU[n]).comp ((r[n]).prodMap (r[n])))
    (hs : (rP[n + 1]).comp (Φ[n + 1]) = (ΦU[n + 1]).comp ((r[n + 1]).prodMap (r[n + 1])))
    (hd : (perfectQcqsConnectingHom j n).comp (ΦU[n + 1]) =
      (projectiveLineSupportedKMap X U n).comp
        ((perfectQcqsConnectingHom U.ι n).prodMap (perfectQcqsConnectingHom U.ι n))) :
    Function.Bijective (projectiveLineSupportedKMap X U n) := by
  have h := perfectQcqs_positiveLongExactSequence U.ι n
  have hP := perfectQcqs_positiveLongExactSequence j n
  exact MonoidHom.bijective_of_mulExact_prodMap
    (r[n + 1]) (perfectQcqsConnectingHom U.ι n) (perfectSupportedKMap U.ι n) (r[n])
    (rP[n + 1]) (perfectQcqsConnectingHom j n) (perfectSupportedKMap j n) (rP[n])
    (Φ[n + 1]) (ΦU[n + 1]) (projectiveLineSupportedKMap X U n) (Φ[n]) (ΦU[n])
    hs hd (projectiveLineSupportedKMap_forget X U n) hn
    (MonoidHom.mulExact_iff.mpr h.1.symm) (MonoidHom.mulExact_iff.mpr h.2.1.symm)
    (MonoidHom.mulExact_iff.mpr h.2.2.symm) (MonoidHom.mulExact_iff.mpr hP.1.symm)
    (MonoidHom.mulExact_iff.mpr hP.2.1.symm) (MonoidHom.mulExact_iff.mpr hP.2.2.symm)
    (projectiveLineKEquiv X (n + 1)).surjective
    (projectiveLineOpenKMap_bijective X U (n + 1))
    (projectiveLineKEquiv X n).bijective (projectiveLineOpenKMap_bijective X U n).injective

/-- The connective projective-line formula on the actual support pair, including K-zero. -/
@[colib_tag "COL-1292",
  colib_ref "ThomasonTrobaugh1990" "Theorem 4.1, (4.1.2)–(4.1.3), p. 329"
    "specialization" "Connective group formula with support for the rank-two trivial bundle"]
def projectiveLineSupportedKEquiv (n : ℕ) :
    PerfectSupportedK U.ι n × PerfectSupportedK U.ι n ≃* PerfectSupportedK j n :=
  MulEquiv.ofBijective (projectiveLineSupportedKMap X U n)
    (projectiveLineSupportedKMap_bijective_of_localizationSquares X U n
      (projectiveLineKMap_restrict X U n) (projectiveLineKMap_restrict X U (n + 1))
      (projectiveLineSupportedKMap_connecting X U n))

end AlgebraicGeometry.Scheme
