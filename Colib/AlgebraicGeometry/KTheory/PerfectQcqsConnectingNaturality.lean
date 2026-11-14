/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectConnectingNaturality
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectOpenKRestriction
public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedPairPullback
public import Colib.AlgebraicGeometry.KTheory.PerfectPullback
public import Colib.AlgebraicGeometry.KTheory.PerfectQcqsConnectiveLocalization
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectSupportedOriginalRestriction
public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedExcision

/-! # The original qcqs fine boundary under geometric pullback

The actual relative boundary and both restriction maps commute with geometric open-pair
pullback. Transport along the unchanged positive relative restriction then identifies the
actual canonical fine boundaries, including the map into supported K-zero.

Sources: `Quillen/AlgebraicGeometry/PerfectComplexes/` files `PairRestriction.lean`,
`ConnectingNaturality.lean`, and `GlobalLocalizationNaturality.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen
universe u d d'
namespace AlgebraicGeometry.Scheme.Modules

/-- The original bounded-flat restriction comparison for the literal geometric pair square. -/
def boundedAboveFlatPerfectOpenPairIso {A B : Scheme.OpenPairs.{u}} (f : A ⟶ B) :
    boundedAboveFlatPerfectPullback f.right ⋙ boundedAboveFlatPerfectPullback A.hom ≅
      boundedAboveFlatPerfectPullback B.hom ⋙ boundedAboveFlatPerfectPullback f.left :=
  (boundedAboveFlatPerfectPullbackCompIso A.hom f.right).symm ≪≫
    eqToIso (congrArg boundedAboveFlatPerfectPullback (MorphismProperty.Arrow.w f).symm) ≪≫
      boundedAboveFlatPerfectPullbackCompIso f.left B.hom

/-- The bounded-flat coarse restriction retains the original pullback square. -/
theorem boundedAboveFlatPerfectOpenKRestrict_pullback {A B : Scheme.OpenPairs.{u}}
    (f : A ⟶ B) (n : ℕ) :
    (boundedAboveFlatPerfectKPullback f.left n).comp
      (boundedAboveFlatPerfectOpenKRestrict B.hom n) =
    (boundedAboveFlatPerfectOpenKRestrict A.hom n).comp
      (boundedAboveFlatPerfectOpenKPullback f n) := by
  unfold boundedAboveFlatPerfectKPullback boundedAboveFlatPerfectOpenKRestrict
    boundedAboveFlatPerfectOpenKPullback
  rw [KMap_comp_KMap, KMap_comp_KMap]
  exact KMap_eq_of_iso _ _ (boundedAboveFlatPerfectOpenPairIso f).symm n

section
variable {A B : Scheme.QuasiCompactOpenPairs.{u}}

/-- The original coarse perfect pullback transported by the literal inclusion equivalence. -/
def perfectOpenKPullback (f : A ⟶ B) (n : ℕ) : PerfectOpenK B.obj.hom n →*
    PerfectOpenK A.obj.hom n :=
  (boundedAboveFlatPerfectOpenKEquiv A.obj.hom n).toMonoidHom.comp
    ((boundedAboveFlatPerfectOpenKPullback f.hom n).comp
      (boundedAboveFlatPerfectOpenKEquiv B.obj.hom n).symm.toMonoidHom)

/-- The coarse pullback agrees with the actual bounded-flat pullback on the literal inclusion. -/
theorem perfectOpenKPullback_comp_boundedFlat (f : A ⟶ B) (n : ℕ) :
    (perfectOpenKPullback f n).comp (boundedAboveFlatPerfectOpenToPerfectOpenKMap B.obj.hom n) =
      (boundedAboveFlatPerfectOpenToPerfectOpenKMap A.obj.hom n).comp
        (boundedAboveFlatPerfectOpenKPullback f.hom n) := by
  ext x
  change boundedAboveFlatPerfectOpenKEquiv A.obj.hom n
    (boundedAboveFlatPerfectOpenKPullback f.hom n
      ((boundedAboveFlatPerfectOpenKEquiv B.obj.hom n).symm
        (boundedAboveFlatPerfectOpenKEquiv B.obj.hom n x))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The unchanged original relative-to-supported boundary is natural under
arbitrary open-pair pullback between qc ambient schemes. -/
theorem perfectOpenConnectingHom_pullback (f : A ⟶ B) (n : ℕ) :
    (perfectSupportedKPullback f n).comp (perfectOpenConnectingHom B.obj.hom n) =
    (perfectOpenConnectingHom A.obj.hom n).comp (perfectOpenKPullback f (n + 1)) := by
  ext x
  obtain ⟨y, rfl⟩ := (boundedAboveFlatPerfectOpenToPerfectOpenKMap_bijective B.obj.hom
    (n + 1)).surjective x
  have hB := DFunLike.congr_fun (boundedAboveFlatPerfectOpenConnectingHom_comparison B.obj.hom n) y
  have hS := DFunLike.congr_fun (perfectSupportedKPullback_comp_boundedFlat f n)
    (boundedAboveFlatPerfectOpenConnectingHom B.obj.hom n y)
  have hF := DFunLike.congr_fun (boundedAboveFlatPerfectOpenConnectingHom_pullback f.hom n) y
  have hA := DFunLike.congr_fun (boundedAboveFlatPerfectOpenConnectingHom_comparison A.obj.hom n)
    (boundedAboveFlatPerfectOpenKPullback f.hom (n + 1) y)
  have hO := DFunLike.congr_fun (perfectOpenKPullback_comp_boundedFlat f (n + 1)) y
  simp only [MonoidHom.comp_apply] at hB hS hF hA hO ⊢
  rw [← hB, hS, hF, hA, hO]

end

/-- The original relative-open restriction is natural for arbitrary open-pair
squares when both opens and both ambient schemes are qc. -/
theorem perfectOpenKRestrict_pullback {A B : AlgebraicGeometry.Scheme.QuasiCompactOpenPairs.{u}}
    [CompactSpace A.obj.left] [CompactSpace B.obj.left] (f : A ⟶ B) (n : ℕ) :
    (perfectKPullback f.hom.left n).comp (perfectOpenKRestrict B.obj.hom n) =
      (perfectOpenKRestrict A.obj.hom n).comp (perfectOpenKPullback f n) := by
  ext x
  obtain ⟨y, rfl⟩ :=
    (boundedAboveFlatPerfectOpenToPerfectOpenKMap_bijective B.obj.hom n).surjective x
  have h₁ := DFunLike.congr_fun (boundedAboveFlatPerfectOpenKRestrict_comparison B.obj.hom n) y
  have h₂ := DFunLike.congr_fun (perfectOpenKPullback_comp_boundedFlat f n) y
  have h₃ := DFunLike.congr_fun (boundedAboveFlatPerfectToPerfectKMap_pullback f.hom.left n)
    (boundedAboveFlatPerfectOpenKRestrict B.obj.hom n y)
  have h₄ := DFunLike.congr_fun (boundedAboveFlatPerfectOpenKRestrict_comparison A.obj.hom n)
    (boundedAboveFlatPerfectOpenKPullback f.hom n y)
  have h₅ := DFunLike.congr_fun (boundedAboveFlatPerfectOpenKRestrict_pullback f.hom n) y
  simp only [MonoidHom.comp_apply] at h₁ h₂ h₃ h₄ h₅ ⊢
  change perfectKPullback f.hom.left n
      (perfectOpenKRestrict B.obj.hom n
        (boundedAboveFlatPerfectOpenToPerfectOpenKMap B.obj.hom n y)) =
    perfectOpenKRestrict A.obj.hom n
      (perfectOpenKPullback f n (boundedAboveFlatPerfectOpenToPerfectOpenKMap B.obj.hom n y))
  exact (congrArg (perfectKPullback f.hom.left n) h₁).trans
    (h₃.trans ((congrArg (boundedAboveFlatPerfectToPerfectKMap A.obj.left.toRingedSpace n) h₅).trans
      (h₄.symm.trans (congrArg (perfectOpenKRestrict A.obj.hom n) h₂.symm))))


/-- The actual target boundary is natural for every commutative square of
qcqs open pairs, with no flatness or cartesianness assumption. -/
theorem perfectQcqsConnectingHom_pullback
    {A B : AlgebraicGeometry.Scheme.QuasiCompactOpenPairs.{u}}
    [QuasiSeparatedSpace ((𝟭 Scheme).obj A.obj.right)]
    [QuasiSeparatedSpace ((𝟭 Scheme).obj B.obj.right)]
    [CompactSpace ((𝟭 Scheme).obj A.obj.left)]
    [CompactSpace ((𝟭 Scheme).obj B.obj.left)]
    [HasDerivedCategory.{d} ((𝟭 Scheme).obj A.obj.left).Modules]
    [HasDerivedCategory.{d'} ((𝟭 Scheme).obj B.obj.left).Modules]
    (f : A ⟶ B) (n : ℕ) :
    (perfectSupportedKPullback f n).comp (perfectQcqsConnectingHom B.obj.hom n) =
      (perfectQcqsConnectingHom A.obj.hom n).comp
        (perfectKPullback (Y := ((𝟭 Scheme).obj B.obj.left)) f.hom.left (n + 1)) := by
  let : CompactSpace A.obj.left := inferInstanceAs
    (CompactSpace ((𝟭 Scheme).obj A.obj.left))
  let : CompactSpace B.obj.left := inferInstanceAs
    (CompactSpace ((𝟭 Scheme).obj B.obj.left))
  ext x
  let : Fact (OpenDerivedImage.HasDerivedRoofs B.obj.hom) :=
    ⟨OpenDerivedImage.hasDerivedRoofs_of_qcqs B.obj.hom⟩
  obtain ⟨a, ha⟩ := (OpenDerivedImage.relativeKRestrictEquiv B.obj.hom
    (OpenDerivedImage.hasPerfectComplements_of_qcqs B.obj.hom) n).surjective x
  change perfectOpenKRestrict B.obj.hom (n + 1) a = x at ha
  subst x
  have h₁ := DFunLike.congr_fun (perfectQcqsConnectingHom_comp_relative B.obj.hom n) a
  have h₂ := DFunLike.congr_fun (perfectOpenConnectingHom_pullback f n) a
  have h₃ := DFunLike.congr_fun (perfectOpenKRestrict_pullback f (n + 1)) a
  have h₄ := DFunLike.congr_fun (perfectQcqsConnectingHom_comp_relative A.obj.hom n)
    (perfectOpenKPullback f (n + 1) a)
  simp only [MonoidHom.comp_apply] at h₁ h₂ h₃ h₄ ⊢
  change perfectSupportedKPullback f n
      (perfectQcqsConnectingHom B.obj.hom n (perfectOpenKRestrict B.obj.hom (n + 1) a)) =
    perfectQcqsConnectingHom A.obj.hom n
      (perfectKPullback f.hom.left (n + 1) (perfectOpenKRestrict B.obj.hom (n + 1) a))
  change perfectSupportedKPullback f n (perfectOpenConnectingHom B.obj.hom n a) =
    perfectOpenConnectingHom A.obj.hom n (perfectOpenKPullback f (n + 1) a) at h₂
  change perfectKPullback f.hom.left (n + 1) (perfectOpenKRestrict B.obj.hom (n + 1) a) =
    perfectOpenKRestrict A.obj.hom (n + 1) (perfectOpenKPullback f (n + 1) a) at h₃
  change perfectQcqsConnectingHom A.obj.hom n
      (perfectOpenKRestrict A.obj.hom (n + 1) (perfectOpenKPullback f (n + 1) a)) =
    perfectOpenConnectingHom A.obj.hom n (perfectOpenKPullback f (n + 1) a) at h₄
  rw [h₁, h₂, h₃, h₄]

section
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- On the canonical support square, restriction is the original bounded-flat pullback. -/
lemma perfectSupportedKRestrict_comp_boundedFlat (n : ℕ) :
    (perfectSupportedKRestrict j T n).comp
        (boundedAboveFlatPerfectSupportedToPerfectKMap T.ι n) =
      (boundedAboveFlatPerfectSupportedToPerfectKMap (j ⁻¹ᵁ T).ι n).comp
        (boundedAboveFlatPerfectSupportedKPullback (Scheme.supportRestrictionPair j T) n) := by
  unfold perfectSupportedKRestrict boundedAboveFlatPerfectSupportedToPerfectKMap
    boundedAboveFlatPerfectSupportedKPullback
  rw [Waldhausen.KMap_comp_KMap, Waldhausen.KMap_comp_KMap]
  exact Waldhausen.KMap_eq_of_iso _ _
    (boundedAboveFlatPerfectSupportedOriginalRestrictionIso j T) n

variable [CompactSpace X] [CompactSpace U]

/-- The native support restriction square viewed in the compact-ambient full subcategory. -/
def qcSupportRestrictionPair :
    (⟨Scheme.supportOpenPair (j ⁻¹ᵁ T), inferInstanceAs (CompactSpace U)⟩ :
      Scheme.QuasiCompactOpenPairs.{u}) ⟶
      (⟨Scheme.supportOpenPair T, inferInstanceAs (CompactSpace X)⟩ :
        Scheme.QuasiCompactOpenPairs.{u}) :=
  ObjectProperty.homMk (Scheme.supportRestrictionPair j T)

/-- The literal exact restriction map is the existing public supported pullback. -/
lemma perfectSupportedKRestrict_eq_pullback (n : ℕ) :
    perfectSupportedKRestrict j T n = perfectSupportedKPullback (qcSupportRestrictionPair j T) n :=
      by
  exact perfectSupportedKPullback_unique (qcSupportRestrictionPair j T) n
    (perfectSupportedKRestrict j T n) (perfectSupportedKRestrict_comp_boundedFlat j T n)

end

end AlgebraicGeometry.Scheme.Modules
