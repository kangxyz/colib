/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.BaseCoverRestrictionPair
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.SupportedBaseOpenRestriction
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.SupportedFineBoundary
public import Colib.AlgebraicGeometry.KTheory.PerfectMayerVietorisBoundaryNaturality
public import Colib.Util.References

/-! # The projective-line map and the Mayer–Vietoris boundary of a base cover -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.PerfectMayerVietoris

namespace AlgebraicGeometry.Scheme

universe u

attribute [local instance] HasDerivedCategory.standard

/-- Transporting the open subset itself induces a natural isomorphism on the
original perfect complexes of the two equal open subschemes. -/
def openCongrPerfect {Y : Scheme.{u}} {A B : Y.Opens} (h : A = B) :
    ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex
      (X := A.toScheme.toRingedSpace)) ⥤
    ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex
      (X := B.toScheme.toRingedSpace)) := by
  subst B
  exact 𝟭 _

/-- The equality-induced identity is exact. -/
theorem openCongrPerfect_exact {Y : Scheme.{u}} {A B : Y.Opens} (h : A = B) :
    IsExact (RingedSpace.perfectComplexesWaldhausen A.toScheme.toRingedSpace).cof
      (RingedSpace.perfectComplexesWaldhausen A.toScheme.toRingedSpace).weq
      (RingedSpace.perfectComplexesWaldhausen B.toScheme.toRingedSpace).cof
      (RingedSpace.perfectComplexesWaldhausen B.toScheme.toRingedSpace).weq
      (openCongrPerfect h) := by
  subst B
  exact IsExact.id _ _

/-- The localization boundary is unchanged by equality of the two open subsets. -/
theorem openCongrPerfect_connecting {Y : Scheme.{u}} [CompactSpace Y]
    [QuasiSeparatedSpace Y] {A B : Y.Opens} [CompactSpace A.toScheme]
    [CompactSpace B.toScheme] (h : A = B) (n : ℕ) :
    (perfectQcqsConnectingHom B.ι n).comp (KMap (openCongrPerfect_exact h) (n + 1)) =
      (KMap (supportedOpenCongr_exact h) n).comp (perfectQcqsConnectingHom A.ι n) := by
  subst B
  have hp : KMap (openCongrPerfect_exact (rfl : A = A)) (n + 1) =
      MonoidHom.id (perfectK A.toScheme (n + 1)) :=
    KMap_id (RingedSpace.perfectComplexesWaldhausen A.toScheme.toRingedSpace) (n + 1)
  have hs : KMap (supportedOpenCongr_exact (rfl : A = A)) n =
      MonoidHom.id (PerfectSupportedK A.ι n) :=
    KMap_id (perfectSupportedWaldhausen A.ι) n
  rw [hp, hs, MonoidHom.comp_id, MonoidHom.id_comp]

/-- On K-groups, the equality transport is the pullback along the induced scheme identity. -/
theorem KMap_openCongrPerfect_eq_pullback {Y : Scheme.{u}} {A B : Y.Opens}
    [CompactSpace A.toScheme] (h : A = B) (n : ℕ) :
    KMap (openCongrPerfect_exact h) n =
      perfectKPullback (eqToHom (congrArg Scheme.Opens.toScheme h.symm)) n := by
  subst B
  have hp : KMap (openCongrPerfect_exact (rfl : A = A)) n =
      MonoidHom.id (perfectK A.toScheme n) :=
    KMap_id (RingedSpace.perfectComplexesWaldhausen A.toScheme.toRingedSpace) n
  rw [hp, eqToHom_refl, perfectKPullback_id]

/-- Equality of opens induces a bijection on their original perfect K-groups. -/
theorem KMap_openCongrPerfect_bijective {Y : Scheme.{u}} {A B : Y.Opens}
    (h : A = B) (n : ℕ) : Function.Bijective (KMap (openCongrPerfect_exact h) n) := by
  subst B
  have hp : KMap (openCongrPerfect_exact (rfl : A = A)) n =
      MonoidHom.id (perfectK A.toScheme n) :=
    KMap_id (RingedSpace.perfectComplexesWaldhausen A.toScheme.toRingedSpace) n
  rw [hp]
  exact Function.bijective_id

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

variable [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace V] [QuasiSeparatedSpace V]
  [CompactSpace T.toScheme] [CompactSpace (j ⁻¹ᵁ T).toScheme]

local instance : IsProper (P ↘ X) := isProper_projectiveSpaceOver 1 X
local instance : IsProper (Q ↘ V) := isProper_projectiveSpaceOver 1 V
local instance : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace (P ↘ X)
local instance : CompactSpace Q := QuasiCompact.compactSpace_of_compactSpace (Q ↘ V)
local instance : QuasiSeparatedSpace P := quasiSeparatedSpace_of_quasiSeparated (P ↘ X)
local instance : QuasiSeparatedSpace Q := quasiSeparatedSpace_of_quasiSeparated (Q ↘ V)
local instance : CompactSpace (Scheme.Opens.toScheme Tₚ) :=
  QuasiCompact.compactSpace_of_compactSpace ((P ↘ X) ∣_ T)
local instance : CompactSpace (Scheme.Opens.toScheme Uₚ) :=
  QuasiCompact.compactSpace_of_compactSpace ((Q ↘ V) ∣_ U)
local instance : CompactSpace (Scheme.Opens.toScheme B) := (e) ▸
  (inferInstance : CompactSpace (Scheme.Opens.toScheme Uₚ))

/-- The map on the overlap uses the actual projective-line map on the inverse-image open. -/
def projectiveLineBaseCoverOverlapKMap (n : ℕ) :
    perfectK (Scheme.Opens.toScheme U) n × perfectK (Scheme.Opens.toScheme U) n →*
      perfectK (Scheme.Opens.toScheme B) n :=
  (KMap (openCongrPerfect_exact e) n).comp (projectiveLineOpenKMap V U n)

omit [IsOpenImmersion j] [CompactSpace X] [QuasiSeparatedSpace X] [QuasiSeparatedSpace V]
  [CompactSpace T.toScheme] in
/-- Restriction from the second member of the cover uses the same inverse-image open. -/
theorem projectiveLineBaseCover_overlapFromV (n : ℕ) :
    (KMap (perfectComplexesRestrictOpenImmersion_isExact (Scheme.Opens.ι B)) n).comp
        (projectiveLineKMap V n) =
      (projectiveLineBaseCoverOverlapKMap j T n).comp
        ((KMap (perfectComplexesRestrictOpenImmersion_isExact (Scheme.Opens.ι U)) n).prodMap
          (KMap (perfectComplexesRestrictOpenImmersion_isExact (Scheme.Opens.ι U)) n)) := by
  let D := eqToHom (congrArg Scheme.Opens.toScheme (e).symm)
  have hι {Y : Scheme.{u}} {C D : Y.Opens} (h : C = D) :
      eqToHom (congrArg Scheme.Opens.toScheme h) ≫ D.ι = C.ι := by
    subst D
    simp
  have hD : D ≫ (Scheme.Opens.ι Uₚ) = (Scheme.Opens.ι B) := hι (e).symm
  unfold projectiveLineBaseCoverOverlapKMap
  rw [KMap_openCongrPerfect_eq_pullback, MonoidHom.comp_assoc,
    ← projectiveLineKMap_restrict V U n, ← MonoidHom.comp_assoc]
  have hcomp :
      (perfectKPullback D n).comp
          (KMap (perfectComplexesRestrictOpenImmersion_isExact (Scheme.Opens.ι Uₚ)) n) =
        KMap (perfectComplexesRestrictOpenImmersion_isExact (Scheme.Opens.ι B)) n := by
    rw [← perfectKPullback_eq_restrict, ← perfectKPullback_comp, hD,
      perfectKPullback_eq_restrict]
  rw [hcomp]

/-- The supported map on the overlap is the same pair of supported summands after equality
of the two inverse-image opens. -/
def projectiveLineBaseCoverSupportedOverlapKMap (n : ℕ) :=
  (KMap (supportedOpenCongr_exact e) n).comp (projectiveLineSupportedKMap V U n)

omit [IsOpenImmersion j] [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace T.toScheme] in
/-- The overlap map and the fine connective localization boundary commute. -/
theorem projectiveLineBaseCoverOverlap_connecting (n : ℕ) :
    (perfectQcqsConnectingHom (Scheme.Opens.ι B) n).comp
      (projectiveLineBaseCoverOverlapKMap j T (n + 1)) =
    (projectiveLineBaseCoverSupportedOverlapKMap j T n).comp
      ((perfectQcqsConnectingHom (Scheme.Opens.ι U) n).prodMap
        (perfectQcqsConnectingHom (Scheme.Opens.ι U) n)) := by
  unfold projectiveLineBaseCoverOverlapKMap projectiveLineBaseCoverSupportedOverlapKMap
  let δ := perfectQcqsConnectingHom (Scheme.Opens.ι Uₚ) n
  let δ' := perfectQcqsConnectingHom (Scheme.Opens.ι B) n
  let k := projectiveLineOpenKMap V U (n + 1)
  let t := KMap (openCongrPerfect_exact e) (n + 1)
  let s := KMap (supportedOpenCongr_exact e) n
  let l := projectiveLineSupportedKMap V U n
  let d := perfectQcqsConnectingHom (Scheme.Opens.ι U) n
  have h₁ : δ'.comp t = s.comp δ := openCongrPerfect_connecting e n
  have h₂ : δ.comp k = l.comp (d.prodMap d) :=
    projectiveLineSupportedKMap_connecting V U n
  exact MonoidHom.ext fun a =>
    (DFunLike.congr_fun h₁ (k a)).trans
      (congrArg s (DFunLike.congr_fun h₂ a))

omit [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace V] [QuasiSeparatedSpace V]
  [CompactSpace T.toScheme] [CompactSpace (j ⁻¹ᵁ T).toScheme] in
/-- The exact supported restriction square for both actual summands. -/
theorem projectiveLineBaseCoverSupportedOverlap_restrict (n : ℕ) :
    (perfectSupportedKRestrict J Tₚ n).comp (projectiveLineSupportedKMap X T n) =
      (projectiveLineBaseCoverSupportedOverlapKMap j T n).comp
        ((perfectSupportedKRestrict j T n).prodMap (perfectSupportedKRestrict j T n)) := by
  let r := perfectSupportedRestrict_exact J Tₚ
  let s := perfectSupportedRestrict_exact j T
  let t := supportedOpenCongr_exact e
  let f := projectiveLineSupportedFirstSummand_exact X T
  let g := projectiveLineSupportedSecondSummand_exact X T
  let f' := projectiveLineSupportedFirstSummand_exact V U
  let g' := projectiveLineSupportedSecondSummand_exact V U
  have h₁ := (KMap_comp_KMap f r n).trans
    ((KMap_eq_of_iso _ _ (projectiveLineSupportedFirstSummand_baseOpenRestrictIso j T) n).trans
      ((KMap_comp_KMap (s.comp f') t n).symm.trans
        (congrArg (fun m => (KMap t n).comp m) (KMap_comp_KMap s f' n).symm)))
  have h₂ := (KMap_comp_KMap g r n).trans
    ((KMap_eq_of_iso _ _ (projectiveLineSupportedSecondSummand_baseOpenRestrictIso j T) n).trans
      ((KMap_comp_KMap (s.comp g') t n).symm.trans
        (congrArg (fun m => (KMap t n).comp m) (KMap_comp_KMap s g' n).symm)))
  refine MonoidHom.ext fun a => ?_
  change (KMap r n) ((KMap f n) a.1 * (KMap g n) a.2) =
    (KMap t n) ((KMap f' n) ((KMap s n) a.1) * (KMap g' n) ((KMap s n) a.2))
  rw [map_mul, map_mul]
  exact congrArg₂ (· * ·) (DFunLike.congr_fun h₁ a.1) (DFunLike.congr_fun h₂ a.2)

omit [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace T.toScheme] in
/-- The projective-line map intertwines the excision-defined Mayer–Vietoris boundary. -/
@[colib_tag "COL-1293"]
theorem projectiveLineBaseCover_connecting
    (hc : ∀ x : X, x ∈ Set.range j ∨ x ∈ T) (n : ℕ) :
    (connectingHom J Tₚ (projectiveLine_baseOpenCover j T hc) n).comp
        (projectiveLineBaseCoverOverlapKMap j T (n + 1)) =
      (projectiveLineKMap X n).comp
        ((connectingHom j T hc n).prodMap (connectingHom j T hc n)) := by
  -- Apply the excision square simultaneously to the two actual summands.
  refine MonoidHom.ext fun x => ?_
  let A := perfectSupportedExcisionKEquiv j T hc n
  let A' := perfectSupportedExcisionKEquiv J Tₚ (projectiveLine_baseOpenCover j T hc) n
  let δ := perfectQcqsConnectingHom (Scheme.Opens.ι U) n
  let δ' := perfectQcqsConnectingHom (Scheme.Opens.ι B) n
  let a := A.symm (δ x.1)
  let b := A.symm (δ x.2)
  have h := DFunLike.congr_fun (projectiveLineBaseCoverSupportedOverlap_restrict j T n) (a, b)
  have hδ := DFunLike.congr_fun (projectiveLineBaseCoverOverlap_connecting j T n) x
  change A' (projectiveLineSupportedKMap X T n (a, b)) =
    projectiveLineBaseCoverSupportedOverlapKMap j T n (A a, A b) at h
  have ha : A a = δ x.1 := A.apply_symm_apply _
  have hb : A b = δ x.2 := A.apply_symm_apply _
  change δ' (projectiveLineBaseCoverOverlapKMap j T (n + 1) x) =
    projectiveLineBaseCoverSupportedOverlapKMap j T n (δ x.1, δ x.2) at hδ
  rw [ha, hb, ← hδ] at h
  have hpre : A'.symm (δ' (projectiveLineBaseCoverOverlapKMap j T (n + 1) x)) =
    projectiveLineSupportedKMap X T n (a, b) := (Equiv.symm_apply_eq A'.toEquiv).2 h.symm
  change perfectSupportedKMap (Scheme.Opens.ι Tₚ) n
    (A'.symm (δ' (projectiveLineBaseCoverOverlapKMap j T (n + 1) x))) =
      projectiveLineKMap X n (perfectSupportedKMap T.ι n a, perfectSupportedKMap T.ι n b)
  rw [hpre]
  exact DFunLike.congr_fun (projectiveLineSupportedKMap_forget X T n) (a, b)

end AlgebraicGeometry.Scheme
