/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.BaseCoverMayerVietoris
public import Colib.AlgebraicGeometry.ProjectiveLine.BaseOpenOverlap
public import Colib.Util.References

/-! # The projective-line map and the ordinary Mayer–Vietoris overlap difference -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.PerfectMayerVietoris

namespace AlgebraicGeometry.Scheme

universe u

variable {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j] (T : X.Opens)

local notation "J" => projectiveSpaceOverMap 1 j
local notation "P" => projectiveSpaceOver 1 X
local notation "Q" => projectiveSpaceOver 1 V
local notation "Tₚ" => Functor.obj (TopologicalSpace.Opens.map (PresheafedSpace.Hom.base
  (LocallyRingedSpace.Hom.toHom (Scheme.Hom.toLRSHom (P ↘ X))))) T
local notation "U" => Functor.obj (TopologicalSpace.Opens.map (PresheafedSpace.Hom.base
  (LocallyRingedSpace.Hom.toHom (Scheme.Hom.toLRSHom j)))) T
local notation "Uₚ" => Functor.obj (TopologicalSpace.Opens.map (PresheafedSpace.Hom.base
  (LocallyRingedSpace.Hom.toHom (Scheme.Hom.toLRSHom (Q ↘ V))))) U
local notation "B" => Functor.obj (TopologicalSpace.Opens.map (PresheafedSpace.Hom.base
  (LocallyRingedSpace.Hom.toHom (Scheme.Hom.toLRSHom J)))) Tₚ
local notation "e" => Eq.symm (projectiveLine_preimage_preimage j T)

local instance : IsOpenImmersion (j.resLE T U le_rfl) := by
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  infer_instance

local instance : IsOpenImmersion ((J).resLE Tₚ B le_rfl) := by
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  infer_instance

variable [CompactSpace T.toScheme] [CompactSpace (j ⁻¹ᵁ T).toScheme]

local instance : IsProper (P ↘ X) := isProper_projectiveSpaceOver 1 X
local instance : IsProper (Q ↘ V) := isProper_projectiveSpaceOver 1 V
local instance : CompactSpace (Scheme.Opens.toScheme Tₚ) :=
  QuasiCompact.compactSpace_of_compactSpace ((P ↘ X) ∣_ T)
local instance : CompactSpace (Scheme.Opens.toScheme Uₚ) :=
  QuasiCompact.compactSpace_of_compactSpace ((Q ↘ V) ∣_ U)
local instance : CompactSpace (Scheme.Opens.toScheme B) := (e) ▸
  (inferInstance : CompactSpace (Scheme.Opens.toScheme Uₚ))

set_option maxHeartbeats 500000 in
-- The comparison elaborates two actual projective base-change pullbacks.
/-- Restriction from the first member uses the base change along the actual overlap map. -/
theorem projectiveLineBaseCover_overlapFromT (n : ℕ) :
    (KMap (perfectComplexesRestrictOpenImmersion_isExact ((J).resLE Tₚ B le_rfl)) n).comp
        (projectiveLineOpenKMap X T n) =
      (projectiveLineBaseCoverOverlapKMap j T n).comp
        ((KMap (perfectComplexesRestrictOpenImmersion_isExact (j.resLE T U le_rfl)) n).prodMap
          (KMap (perfectComplexesRestrictOpenImmersion_isExact (j.resLE T U le_rfl)) n)) := by
  let a := j.resLE T U le_rfl
  let A := (J).resLE Tₚ B le_rfl
  let x := projectiveLineOpenBaseChangeIso X T
  let y := projectiveLineOpenBaseChangeIso V U
  let d := eqToHom (congrArg Scheme.Opens.toScheme (e).symm)
  let d' := eqToHom (congrArg Scheme.Opens.toScheme (e))
  let p := projectiveSpaceOverMap 1 a
  let : IsProper (projectiveSpaceOver 1 T.toScheme ↘ T.toScheme) :=
    isProper_projectiveSpaceOver 1 T.toScheme
  let : IsProper (projectiveSpaceOver 1 (Scheme.Opens.toScheme U) ↘ (Scheme.Opens.toScheme U)) :=
    isProper_projectiveSpaceOver 1 (Scheme.Opens.toScheme U)
  let : CompactSpace (projectiveSpaceOver 1 T.toScheme) :=
    QuasiCompact.compactSpace_of_compactSpace (projectiveSpaceOver 1 T.toScheme ↘ T.toScheme)
  let : CompactSpace (projectiveSpaceOver 1 (Scheme.Opens.toScheme U)) :=
    QuasiCompact.compactSpace_of_compactSpace
      (projectiveSpaceOver 1 (Scheme.Opens.toScheme U) ↘ (Scheme.Opens.toScheme U))
  have h : A ≫ x.inv = d ≫ y.inv ≫ p := by
    have hs : y.hom ≫ d' ≫ A = p ≫ x.hom := projectiveLineBaseOpenOverlap_square j T
    have hd : d ≫ d' = 𝟙 _ := (eqToHom_trans _ _).trans (eqToHom_refl _ _)
    calc
      A ≫ x.inv = d ≫ y.inv ≫ (y.hom ≫ d' ≫ A) ≫ x.inv := by
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        rw [← Category.assoc d d', hd, Category.id_comp]
      _ = d ≫ y.inv ≫ p := by rw [hs]; simp
  let r := KMap (perfectComplexesRestrictOpenImmersion_isExact a) n
  let R := KMap (perfectComplexesRestrictOpenImmersion_isExact A) n
  let S := KMap (perfectComplexesRestrictOpenImmersion_isExact p) n
  have hs : S.comp (projectiveLineKMap T.toScheme n) =
      (projectiveLineKMap (Scheme.Opens.toScheme U) n).comp (r.prodMap r) :=
    projectiveLineKMap_baseOpenRestrict a n
  have hd' : KMap (openCongrPerfect_exact e) n = perfectKPullback d n :=
    KMap_openCongrPerfect_eq_pullback e n
  have hK : R.comp (perfectKPullback x.inv n) =
      (perfectKPullback d n).comp ((perfectKPullback y.inv n).comp S) := by
    change (KMap (perfectComplexesRestrictOpenImmersion_isExact A) n).comp _ =
      (perfectKPullback d n).comp
        ((perfectKPullback y.inv n).comp
          (KMap (perfectComplexesRestrictOpenImmersion_isExact p) n))
    rw [← perfectKPullback_eq_restrict A n, ← perfectKPullback_eq_restrict p n,
      ← perfectKPullback_comp, ← perfectKPullback_comp, ← perfectKPullback_comp, h]
  refine MonoidHom.ext fun z => ?_
  change R (perfectKPullback x.inv n (projectiveLineKMap T.toScheme n z)) =
    KMap (openCongrPerfect_exact e) n
      (perfectKPullback y.inv n (projectiveLineKMap (Scheme.Opens.toScheme U) n
        ((r.prodMap r) z)))
  rw [hd']
  exact (DFunLike.congr_fun hK (projectiveLineKMap T.toScheme n z)).trans
    (congrArg (fun w => perfectKPullback d n (perfectKPullback y.inv n w))
      (DFunLike.congr_fun hs z))

local instance (Y : Scheme.{u}) (n : ℕ) : CommGroup (perfectK Y n) :=
  Additivity.KCommGroup (RingedSpace.perfectComplexesWaldhausen Y.toRingedSpace) n

variable [CompactSpace V]

/-- The projective-line map commutes with the ordinary overlap difference, with its fixed sign. -/
@[colib_tag "COL-1293"]
theorem projectiveLineBaseCover_overlapDifference (n : ℕ) :
    (overlapDifference J Tₚ n).comp (projectiveLineBaseCoverPairKMap (V := V) T n) =
      (projectiveLineBaseCoverOverlapKMap j T n).comp
        (GroupMayerVietoris.difference
          ((KMap (perfectComplexesRestrictOpenImmersion_isExact (j.resLE T U le_rfl)) n).prodMap
            (KMap (perfectComplexesRestrictOpenImmersion_isExact (j.resLE T U le_rfl)) n))
          ((KMap (perfectComplexesRestrictOpenImmersion_isExact (Scheme.Opens.ι U)) n).prodMap
            (KMap (perfectComplexesRestrictOpenImmersion_isExact (Scheme.Opens.ι U)) n))) := by
  exact GroupMayerVietoris.difference_natural _ _ _ _ _ _ _
    (projectiveLineBaseCover_overlapFromT j T n) (projectiveLineBaseCover_overlapFromV j T n)

end AlgebraicGeometry.Scheme
