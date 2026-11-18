/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Sheafification
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Zariski.Sheafification.LocalZero
import Colib.AlgebraicGeometry.PresheavesWithTransfers.Sheafification.HomotopyInvariance
import Colib.AlgebraicGeometry.PresheavesWithTransfers.Sheafification.Image
import Colib.AlgebraicGeometry.SheavesWithTransfers.Exactness

/-!
# Zariski sheafification of homotopy invariant presheaves with transfers

The canonical map from the ordinary Zariski sheafification to the underlying
Nisnevich sheafification is invertible for homotopy invariant coefficients over
any field. The proof applies Zariski local vanishing to the kernel and cokernel
of the transfer-natural unit. The comparison identifies the original units
and gives the transfer action by the already constructed Nisnevich sheafification.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme SmoothSite.Contraction

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

local notation "JZar" => SmoothSite.zariskiTopology (Spec (CommRingCat.of k))
local notation "JNis" => SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))
set_option hygiene false in
set_option quotPrecheck false in
local notation "Z" => (toPresheaf.{u + 1} k ⋙ presheafToSheaf JZar AddCommGrpCat.{u + 1})
set_option hygiene false in
set_option quotPrecheck false in
local notation "N" => (toPresheaf.{u + 1} k ⋙ presheafToSheaf JNis AddCommGrpCat.{u + 1})
set_option hygiene false in
set_option quotPrecheck false in
local notation "NZ" => (nisnevichSheafify k ⋙ SheafWithTransfers.toSheaf k ⋙
  SmoothSite.nisnevichToZariskiSheaf (Spec (CommRingCat.of k)) AddCommGrpCat.{u + 1})

/-- The canonical comparison extends the transfer-natural Nisnevich unit
along ordinary Zariski sheafification of the graph restriction. -/
def zariskiSheafifyUnderlyingComparison (P : PresheafWithTransfers.{u + 1} k) :
    (Z).obj P ⟶ (NZ).obj P :=
  ⟨sheafifyLift JZar ((toPresheaf k).map (toNisnevichSheafify k P)) ((NZ).obj P).property⟩

/-- The comparison carries the ordinary Zariski unit to the restriction of the transfer unit. -/
@[reassoc (attr := simp)]
theorem toSheafify_zariskiSheafifyUnderlyingComparison (P : PresheafWithTransfers.{u + 1} k) :
    toSheafify JZar ((toPresheaf k).obj P) ≫ (zariskiSheafifyUnderlyingComparison P).hom =
      (toPresheaf k).map (toNisnevichSheafify k P) :=
  toSheafify_sheafifyLift _ _ _

/-- The ordinary sheafification comparison is natural in the original coefficient maps. -/
@[reassoc]
theorem zariskiSheafifyUnderlyingComparison_naturality
    {P Q : PresheafWithTransfers.{u + 1} k} (f : P ⟶ Q) :
    (Z).map f ≫ zariskiSheafifyUnderlyingComparison Q =
      zariskiSheafifyUnderlyingComparison P ≫ (NZ).map f := by
  apply ObjectProperty.hom_ext
  apply sheafify_hom_ext JZar _ _ ((NZ).obj Q).property
  change toSheafify JZar _ ≫ (sheafifyMap JZar ((toPresheaf k).map f) ≫
    (zariskiSheafifyUnderlyingComparison Q).hom) =
      toSheafify JZar _ ≫ ((zariskiSheafifyUnderlyingComparison P).hom ≫
        (toPresheaf k).map ((nisnevichSheafify k).map f).hom)
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
    toSheafify_zariskiSheafifyUnderlyingComparison, ← Category.assoc,
    toSheafify_zariskiSheafifyUnderlyingComparison, ← Functor.map_comp, ← Functor.map_comp,
    toNisnevichSheafify_naturality]

private theorem isA1Invariant_of_mono_app {P Q : PresheafWithTransfers.{u + 1} k} (f : P ⟶ Q)
    [∀ X : Cor k, Mono (f.hom.app (op X))] (hQ : Q.IsA1Invariant) :
    P.IsA1Invariant := by
  intro X
  let R := CommRingCat.of k
  let P₀ := (toPresheaf k).obj P
  let Q₀ := (toPresheaf k).obj Q
  let φ := (toPresheaf k).map f
  let p := A1.projectionPullback R P₀ X
  let s := A1.sectionPullback R P₀ X 0
  have hs : s ≫ p = 𝟙 _ := by
    let Y := affineLineCylinder.obj X
    let : Mono (φ.app (op Y)) := inferInstanceAs (Mono (f.hom.app (op (Cor.mk Y))))
    apply (cancel_mono (φ.app (op Y))).mp
    have hn := φ.naturality (nativeAffineSection R X 0).op
    have hm := φ.naturality ((projection (SmoothSite.additiveGroupObject (Spec R))).app X).op
    change s ≫ φ.app (op X) = φ.app (op Y) ≫ A1.sectionPullback R Q₀ X 0 at hn
    change p ≫ φ.app (op Y) = φ.app (op X) ≫ A1.projectionPullback R Q₀ X at hm
    rw [Category.assoc, hm, ← Category.assoc, hn, Category.assoc,
      A1.sectionPullback_projectionPullback R Q₀ hQ X 0, Category.comp_id, Category.id_comp]
  exact ⟨⟨s, A1.projectionPullback_sectionPullback R P₀ X 0, hs⟩⟩

private theorem isIso_zariskiSheafify_map_toNisnevichSheafify
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    IsIso ((Z).map (toNisnevichSheafify k P)) := by
  let η := toNisnevichSheafify k P
  let f := (toPresheaf k).map η
  let : Presheaf.IsLocallyInjective JNis f := isLocallyInjective_toNisnevichSheafify k P
  let : Presheaf.IsLocallySurjective JNis f := isLocallySurjective_toNisnevichSheafify k P
  let := SmoothSite.wEqualsLocallyBijective_addCommGrpCat JNis
  let : IsIso ((N).map η) := ((JNis).W_iff f).mp ((JNis).W_of_isLocallyBijective f)
  let : Mono ((N).map η) := IsIso.mono_of_iso ((N).map η)
  let : Epi ((N).map η) := IsIso.epi_of_iso ((N).map η)
  let E (X : Cor k) := PresheafWithTransfers.forget ⋙
    (CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj (op X)
  let (X : Cor k) : Mono ((kernel.ι η).hom.app (op X)) :=
    inferInstanceAs (Mono ((E X).map (kernel.ι η)))
  let (X : Cor k) : Epi ((cokernel.π η).hom.app (op X)) :=
    inferInstanceAs (Epi ((E X).map (cokernel.π η)))
  have hK : (kernel η).IsA1Invariant := isA1Invariant_of_mono_app (kernel.ι η) hP
  have hC : (cokernel η).IsA1Invariant :=
    isA1Invariant_of_epi_app (cokernel.π η) (nisnevichSheafify_isA1Invariant P hP)
  have hnK : IsZero ((N).obj (kernel η)) :=
    (isZero_kernel_of_mono ((N).map η)).of_iso (PreservesKernel.iso N η)
  have hnC : IsZero ((N).obj (cokernel η)) :=
    (isZero_cokernel_of_epi ((N).map η)).of_iso (PreservesCokernel.iso N η)
  have hzK : IsZero (kernel ((Z).map η)) :=
    (isZero_zariskiSheafify_of_isZero_nisnevichSheafify _ hK hnK).of_iso
      (PreservesKernel.iso Z η).symm
  have hzC : IsZero (cokernel ((Z).map η)) :=
    (isZero_zariskiSheafify_of_isZero_nisnevichSheafify _ hC hnC).of_iso
      (PreservesCokernel.iso Z η).symm
  let : Mono ((Z).map η) := Abelian.mono_of_kernel_ι_eq_zero _ (hzK.eq_zero_of_src _)
  let : Epi ((Z).map η) := Abelian.epi_of_cokernel_π_eq_zero _ (hzC.eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi _

/-- The canonical Zariski to Nisnevich comparison is invertible for every
homotopy invariant transfer presheaf. -/
@[colib_tag "COL-1306", colib_ref "MVW2006" "Lecture 22, Theorem 22.2" "adaptation"
  "Canonical comparison of ordinary Zariski and Nisnevich sheafifications over a field"]
theorem isIso_zariskiSheafifyUnderlyingComparison
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    IsIso (zariskiSheafifyUnderlyingComparison P) := by
  let Q := (NZ).obj P
  let η := toNisnevichSheafify k P
  let c := zariskiSheafifyUnderlyingComparison P
  have hc : c.hom ≫ toSheafify JZar Q.obj = ((Z).map η).hom := by
    apply sheafify_hom_ext JZar _ _
      ((presheafToSheaf JZar AddCommGrpCat.{u + 1}).obj Q.obj).property
    rw [← Category.assoc]
    change (toSheafify JZar _ ≫ (zariskiSheafifyUnderlyingComparison P).hom) ≫
      toSheafify JZar Q.obj = toSheafify JZar _ ≫ sheafifyMap JZar ((toPresheaf k).map η)
    rw [toSheafify_zariskiSheafifyUnderlyingComparison, toSheafify_naturality]
  let : IsIso (toSheafify JZar Q.obj) := isIso_toSheafify _ Q.property
  let : IsIso ((Z).map η) := isIso_zariskiSheafify_map_toNisnevichSheafify P hP
  let : IsIso (((Z).map η).hom) :=
    inferInstanceAs (IsIso ((sheafToPresheaf JZar _).map ((Z).map η)))
  exact (ObjectProperty.isIso_hom_iff c).mp (IsIso.of_isIso_fac_right hc)

/-- The canonical unit-compatible identification of ordinary Zariski
sheafification with the underlying Nisnevich sheafification. -/
def zariskiSheafificationUnderlyingIso
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    (Z).obj P ≅ (NZ).obj P := by
  let := isIso_zariskiSheafifyUnderlyingComparison P hP
  exact asIso (zariskiSheafifyUnderlyingComparison P)

/-- The isomorphism identifies the two canonical units on the graph restriction. -/
@[reassoc (attr := simp)]
theorem toSheafify_zariskiSheafificationUnderlyingIso
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    toSheafify JZar ((toPresheaf k).obj P) ≫ (zariskiSheafificationUnderlyingIso P hP).hom.hom =
      (toPresheaf k).map (toNisnevichSheafify k P) :=
  toSheafify_zariskiSheafifyUnderlyingComparison P

/-- Ordinary Zariski sheafification preserves homotopy invariance after graph restriction. -/
@[colib_tag "COL-1306", colib_ref "MVW2006" "Lecture 22, Theorem 22.1" "adaptation"
  "Homotopy invariance of the ordinary Zariski sheafification over a field"]
theorem zariskiSheafify_isA1Invariant
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    A1.IsInvariant (.of k) (sheafify JZar ((toPresheaf k).obj P)) := by
  intro X
  let c := (sheafToPresheaf JZar AddCommGrpCat.{u + 1}).mapIso
    (zariskiSheafificationUnderlyingIso P hP)
  exact (NatIso.isIso_map_iff c
    ((projection (SmoothSite.additiveGroupObject (Spec (.of k)))).app X).op).mpr
      (nisnevichSheafify_isA1Invariant P hP X)

/-- The graph restriction of a homotopy invariant Zariski sheaf with
transfers already satisfies Nisnevich descent. -/
theorem isNisnevichSheaf_of_isZariskiSheaf
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (hZ : Presheaf.IsSheaf JZar ((toPresheaf k).obj P)) :
    IsNisnevichSheaf k P := by
  let e := isoSheafify JZar hZ ≪≫
    (sheafToPresheaf JZar AddCommGrpCat.{u + 1}).mapIso (zariskiSheafificationUnderlyingIso P hP)
  exact (Presheaf.isSheaf_of_iso_iff (J := JNis) e).mpr ((nisnevichSheafify k).obj P).property

private theorem isIso_of_isIso_toPresheaf_map {P Q : PresheafWithTransfers.{u + 1} k}
    (f : P ⟶ Q) (h : IsIso ((toPresheaf k).map f)) : IsIso f := by
  let := h
  apply (ObjectProperty.isIso_hom_iff f).mp
  apply (NatTrans.isIso_iff_isIso_app f.hom).mpr
  intro X
  change IsIso (((toPresheaf k).map f).app (op X.unop.toSmoothSite))
  infer_instance

set_option maxHeartbeats 600000 in
-- Keep the original transfer lift and the underlying sheafification comparison explicit.
/-- Any transfer structure realizing ordinary Zariski sheafification and
making its unit transfer-natural is uniquely isomorphic to the existing
transfer-preserving Nisnevich sheafification, with the prescribed underlying
ordinary identification. -/
@[colib_tag "COL-1306", colib_ref "MVW2006" "Lecture 22, Theorem 22.15" "adaptation"
  "Unique transfer isomorphism fixing the identified ordinary sheafification and unit"]
theorem existsUnique_zariskiSheafify_transferIso
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (Q : PresheafWithTransfers.{u + 1} k) (η : P ⟶ Q)
    (e : sheafify JZar ((toPresheaf k).obj P) ≅ (toPresheaf k).obj Q)
    (he : toSheafify JZar ((toPresheaf k).obj P) ≫ e.hom = (toPresheaf k).map η) :
    ∃! i : ((nisnevichSheafify k).obj P).obj ≅ Q,
      toNisnevichSheafify k P ≫ i.hom = η ∧ (toPresheaf k).mapIso i =
        ((sheafToPresheaf JZar AddCommGrpCat.{u + 1}).mapIso
          (zariskiSheafificationUnderlyingIso P hP)).symm ≪≫ e := by
  let c := (sheafToPresheaf JZar AddCommGrpCat.{u + 1}).mapIso
    (zariskiSheafificationUnderlyingIso P hP)
  have hQ : Presheaf.IsSheaf JNis ((toPresheaf k).obj Q) :=
    (Presheaf.isSheaf_of_iso_iff (J := JNis) (c.symm ≪≫ e)).mp
      ((nisnevichSheafify k).obj P).property
  let Q' : SheafWithTransfers.{u + 1} k := ⟨Q, hQ⟩
  let θ : ((nisnevichSheafify k).obj P).obj ⟶ Q := (nisnevichSheafifyLift k (Q := Q') η).hom
  have hθunit : toNisnevichSheafify k P ≫ θ = η := toNisnevichSheafify_lift k (Q := Q') η
  have hc : c.hom ≫ (toPresheaf k).map θ = e.hom := by
    apply sheafify_hom_ext JZar _ _
      (hQ.of_le (SmoothSite.zariskiTopology_le_nisnevichTopology (Spec (.of k))))
    rw [← Category.assoc]
    change (toSheafify JZar _ ≫ (zariskiSheafificationUnderlyingIso P hP).hom.hom) ≫
      (toPresheaf k).map θ = _
    rw [toSheafify_zariskiSheafificationUnderlyingIso, ← Functor.map_comp, hθunit, he]
  let : IsIso θ := isIso_of_isIso_toPresheaf_map θ (IsIso.of_isIso_fac_left hc)
  have hθ : (toPresheaf k).mapIso (asIso θ) = c.symm ≪≫ e := by
    apply Iso.ext
    exact c.eq_inv_comp.mpr hc
  refine ⟨asIso θ, ⟨hθunit, hθ⟩, fun i hi => ?_⟩
  apply Iso.ext
  apply (toPresheaf k).map_injective
  exact congrArg Iso.hom (hi.2.trans hθ.symm)

end AlgebraicGeometry.PresheafWithTransfers
