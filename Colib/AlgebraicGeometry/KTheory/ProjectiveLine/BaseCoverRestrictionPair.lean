/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.BaseOpenRestriction
public import Colib.AlgebraicGeometry.KTheory.PerfectMayerVietoris
public import Colib.Algebra.Group.MayerVietorisNaturality
public import Colib.Util.References

/-! # Restriction of the projective-line map to the two members of a base cover -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.PerfectMayerVietoris

namespace AlgebraicGeometry.Scheme

universe u

variable {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j] (T : X.Opens)

local notation "J" => projectiveSpaceOverMap 1 j
local notation "P" => projectiveSpaceOver 1 X
local notation "Tₚ" => Functor.obj (TopologicalSpace.Opens.map (PresheafedSpace.Hom.base
  (LocallyRingedSpace.Hom.toHom (Scheme.Hom.toLRSHom (P ↘ X))))) T

/-- The actual formula commutes with the base-open restriction. -/
theorem projectiveLineKMap_baseOpenRestrict (n : ℕ) :
    (KMap (perfectComplexesRestrictOpenImmersion_isExact J) n).comp
      (projectiveLineKMap X n) =
    (projectiveLineKMap V n).comp
      ((KMap (perfectComplexesRestrictOpenImmersion_isExact j) n).prodMap
        (KMap (perfectComplexesRestrictOpenImmersion_isExact j) n)) := by
  let r := perfectComplexesRestrictOpenImmersion_isExact J
  let s := perfectComplexesRestrictOpenImmersion_isExact j
  let f := projectiveLineFirstSummand_exact X
  let g := projectiveLineSecondSummand_exact X
  let f' := projectiveLineFirstSummand_exact V
  let g' := projectiveLineSecondSummand_exact V
  have h₁ := (KMap_comp_KMap f r n).trans
    ((KMap_eq_of_iso _ _ (projectiveLineFirstSummand_baseOpenRestrictIso j) n).trans
      (KMap_comp_KMap s f' n).symm)
  have h₂ := (KMap_comp_KMap g r n).trans
    ((KMap_eq_of_iso _ _ (projectiveLineSecondSummand_baseOpenRestrictIso j) n).trans
      (KMap_comp_KMap s g' n).symm)
  refine MonoidHom.ext fun a => ?_
  change (KMap r n) (projectiveLineKMap X n (a.1, a.2)) =
    projectiveLineKMap V n ((KMap s n) a.1, (KMap s n) a.2)
  rw [projectiveLineKMap_apply, projectiveLineKMap_apply, map_mul]
  exact congrArg₂ (· * ·) (DFunLike.congr_fun h₁ a.1) (DFunLike.congr_fun h₂ a.2)

variable [CompactSpace T.toScheme]

local notation "Q" => projectiveSpaceOver 1 V

local instance : IsProper (P ↘ X) := isProper_projectiveSpaceOver 1 X
local instance : IsProper (Q ↘ V) := isProper_projectiveSpaceOver 1 V
local instance : CompactSpace (Scheme.Opens.toScheme Tₚ) :=
  QuasiCompact.compactSpace_of_compactSpace ((P ↘ X) ∣_ T)

/-- The two component maps on a cover, in the original order with the open subset first. -/
def projectiveLineBaseCoverPairKMap (n : ℕ) :=
  (projectiveLineOpenKMap X T n).prodMap (projectiveLineKMap V n)

/-- The projective-line map commutes with the ordinary Mayer–Vietoris restriction pair. -/
@[colib_tag "COL-1293"]
theorem projectiveLineBaseCover_restrictionPair (n : ℕ) :
    (restrictionPair J Tₚ n).comp (projectiveLineKMap X n) =
      (projectiveLineBaseCoverPairKMap (V := V) T n).comp
        (GroupMayerVietoris.pair
          ((KMap (perfectComplexesRestrictOpenImmersion_isExact T.ι) n).prodMap
            (KMap (perfectComplexesRestrictOpenImmersion_isExact T.ι) n))
          ((KMap (perfectComplexesRestrictOpenImmersion_isExact j) n).prodMap
            (KMap (perfectComplexesRestrictOpenImmersion_isExact j) n))) := by
  exact GroupMayerVietoris.pair_natural _ _ _ _ _ _ _
    (projectiveLineKMap_restrict X T n) (projectiveLineKMap_baseOpenRestrict j n)

end AlgebraicGeometry.Scheme
