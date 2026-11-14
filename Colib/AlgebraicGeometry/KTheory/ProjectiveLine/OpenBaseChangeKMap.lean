/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectPullbackCompatibility
public import Colib.AlgebraicGeometry.ProjectiveLine.OpenBaseChange
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.DiagonalSurjectivity

/-! # Fine K-theory of the inverse-image projective-line open -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen AlgebraicGeometry.RingedSpace
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u}) (U : X.Opens) [CompactSpace U.toScheme]

local notation "P" => projectiveSpaceOver 1 X
local notation "π" => (P ↘ X)
local notation "Q" => projectiveSpaceOver 1 U.toScheme
local notation "V" => Functor.obj
  (TopologicalSpace.Opens.map (PresheafedSpace.Hom.base
    (LocallyRingedSpace.Hom.toHom (Scheme.Hom.toLRSHom π)))) U
local notation "Y" => Scheme.Opens.toScheme V
local notation:max "W[" Z "]" =>
  perfectComplexesWaldhausen (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace Z))
local notation "e" => projectiveLineOpenBaseChangeIso X U

/-- The projective-line formula on the literal inverse-image open, with its unchanged K-map. -/
def projectiveLineOpenKMap (n : ℕ) :
    (W[U.toScheme]).K n × (W[U.toScheme]).K n →* (W[Y]).K n := by
  let : IsProper (Q ↘ U.toScheme) := isProper_projectiveSpaceOver 1 U.toScheme
  let : CompactSpace Q := QuasiCompact.compactSpace_of_compactSpace (Q ↘ U.toScheme)
  exact (perfectKPullback (e).inv n).comp (projectiveLineKMap U.toScheme n)

/-- The open vertical map is bijective in every connective degree, including zero. -/
theorem projectiveLineOpenKMap_bijective (n : ℕ) :
    Function.Bijective (projectiveLineOpenKMap X U n) := by
  let : IsProper (Q ↘ U.toScheme) := isProper_projectiveSpaceOver 1 U.toScheme
  let : CompactSpace Q := QuasiCompact.compactSpace_of_compactSpace (Q ↘ U.toScheme)
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (e).inv
  have h₁ : (perfectKPullback (e).hom n).comp (perfectKPullback (e).inv n) =
      MonoidHom.id ((W[Q]).K n) := by
    rw [← perfectKPullback_comp, Iso.hom_inv_id, perfectKPullback_id]
  have h₂ : (perfectKPullback (e).inv n).comp (perfectKPullback (e).hom n) =
      MonoidHom.id ((W[Y]).K n) := by
    rw [← perfectKPullback_comp, Iso.inv_hom_id, perfectKPullback_id]
  have hb : Function.Bijective (perfectKPullback (e).inv n) :=
    ⟨(show Function.LeftInverse (perfectKPullback (e).hom n)
        (perfectKPullback (e).inv n) from fun a => DFunLike.congr_fun h₁ a).injective,
      (show Function.RightInverse (perfectKPullback (e).hom n)
        (perfectKPullback (e).inv n) from fun a => DFunLike.congr_fun h₂ a).surjective⟩
  exact hb.comp (projectiveLineKEquiv U.toScheme n).bijective

end AlgebraicGeometry.Scheme
