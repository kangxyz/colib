/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SupportedForget
public import Colib.AlgebraicGeometry.KTheory.PerfectPullbackCompatibility
public import Colib.AlgebraicGeometry.KTheory.PerfectQcqsConnectingNaturality

/-! # Naturality of connective localization for qcqs open pairs

The positive relative-to-open comparison and the three maps of the connective localization
sequence commute with pullback along a commutative square of quasi-compact open pairs with
quasi-separated ambient schemes. Neither flatness nor cartesianness is needed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Waldhausen

namespace AlgebraicGeometry.Scheme.Modules

universe u d d'

local instance (A : QuasiCompactOpenPairs.{u}) : CompactSpace A.obj.right := A.property

/-- The positive relative-to-open equivalence for a qcqs pair uses the actual restriction. -/
def perfectQcqsOpenKEquiv {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace U] (j : U ⟶ X) [IsOpenImmersion j] [HasDerivedCategory.{d} U.Modules]
    (n : ℕ) : PerfectOpenK j (n + 1) ≃*
    (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace).K (n + 1) := by
  letI : Fact (OpenDerivedImage.HasDerivedRoofs j) :=
    ⟨OpenDerivedImage.hasDerivedRoofs_of_qcqs j⟩
  exact OpenDerivedImage.relativeKRestrictEquiv j (OpenDerivedImage.hasPerfectComplements_of_qcqs j) n

@[simp]
theorem perfectQcqsOpenKEquiv_apply {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace U] (j : U ⟶ X) [IsOpenImmersion j] [HasDerivedCategory.{d} U.Modules]
    (n : ℕ) (a : PerfectOpenK j (n + 1)) :
    perfectQcqsOpenKEquiv j n a = perfectOpenKRestrict j (n + 1) a := rfl

variable {A B : QuasiCompactOpenPairs.{u}}
  [QuasiSeparatedSpace ((𝟭 Scheme).obj A.obj.right)]
  [QuasiSeparatedSpace ((𝟭 Scheme).obj B.obj.right)]
  [CompactSpace ((𝟭 Scheme).obj A.obj.left)]
  [CompactSpace ((𝟭 Scheme).obj B.obj.left)]
  [HasDerivedCategory.{d} ((𝟭 Scheme).obj A.obj.left).Modules]
  [HasDerivedCategory.{d'} ((𝟭 Scheme).obj B.obj.left).Modules]

/-- The inverse positive comparison intertwines the relative-open and ordinary pullbacks. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/GlobalLocalizationNaturality.lean:56-84"
  "adaptation" "Naturality of the inverse of actual positive open restriction"]
theorem perfectQcqsOpenKEquiv_symm_pullback (f : A ⟶ B) (n : ℕ) :
    (perfectOpenKPullback f (n + 1)).comp
        (perfectQcqsOpenKEquiv B.obj.hom n).symm.toMonoidHom =
      (perfectQcqsOpenKEquiv A.obj.hom n).symm.toMonoidHom.comp
        (perfectKPullback (Y := ((𝟭 Scheme).obj B.obj.left)) f.hom.left (n + 1)) := by
  let : CompactSpace B.obj.left := inferInstanceAs (CompactSpace ((𝟭 Scheme).obj B.obj.left))
  ext x
  apply (perfectQcqsOpenKEquiv A.obj.hom n).injective
  have h := DFunLike.congr_fun (perfectOpenKRestrict_pullback f (n + 1))
    ((perfectQcqsOpenKEquiv B.obj.hom n).symm x)
  simp only [MonoidHom.comp_apply] at h
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [MulEquiv.apply_symm_apply, perfectQcqsOpenKEquiv_apply, ← h]
  change perfectKPullback f.hom.left (n + 1)
      (perfectQcqsOpenKEquiv B.obj.hom n ((perfectQcqsOpenKEquiv B.obj.hom n).symm x)) = _
  rw [MulEquiv.apply_symm_apply]

/-- The supported boundary, forgetting support, and open restriction in the connective
localization sequence all commute with a morphism of qcqs open pairs. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/GlobalLocalizationNaturality.lean:86-104"
  "adaptation" "All three naturality squares on the actual connective localization maps"]
theorem perfectQcqsLongExactSequence_pullback (f : A ⟶ B) (n : ℕ) :
    (perfectSupportedKPullback f n).comp (perfectQcqsConnectingHom B.obj.hom n) =
        (perfectQcqsConnectingHom A.obj.hom n).comp
          (perfectKPullback (Y := ((𝟭 Scheme).obj B.obj.left)) f.hom.left (n + 1)) ∧
      (perfectKPullback f.hom.right n).comp (perfectSupportedKMap B.obj.hom n) =
        (perfectSupportedKMap A.obj.hom n).comp (perfectSupportedKPullback f n) ∧
      (perfectKPullback (Y := ((𝟭 Scheme).obj B.obj.left)) f.hom.left n).comp
          (KMap (perfectComplexesRestrictOpenImmersion_isExact B.obj.hom) n) =
        (KMap (perfectComplexesRestrictOpenImmersion_isExact A.obj.hom) n).comp
          (perfectKPullback f.hom.right n) := by
  let : CompactSpace B.obj.left := inferInstanceAs (CompactSpace ((𝟭 Scheme).obj B.obj.left))
  have hw : A.obj.hom ≫ f.hom.right = f.hom.left ≫ B.obj.hom := by
    first | exact MorphismProperty.Arrow.w f.hom | exact (MorphismProperty.Arrow.w f.hom).symm
  exact ⟨perfectQcqsConnectingHom_pullback f n, perfectSupportedKMap_pullback f n,
    (perfectKPullback_restrict_square A.obj.hom B.obj.hom f.hom.right f.hom.left
      hw n).symm⟩

end AlgebraicGeometry.Scheme.Modules
