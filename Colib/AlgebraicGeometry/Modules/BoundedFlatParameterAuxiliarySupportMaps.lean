/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatGlobalSupportedPairDiagram
public import Colib.AlgebraicGeometry.Morphisms.OpenImmersion.Pair.Support

/-! # Original parameter support enlargement and supported restriction

The three original supported Models vanish on the union, the auxiliary open,
and its inverse image. Their maps are induced by actual open-pair squares.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
namespace ParameterAuxiliarySupport

/-- The original product map in the fixed factor, without an openness assumption. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliarySupportMaps.lean:29"
  "adaptation" "Original actual open-pair maps, unchanged support and chosen zero."]
def productMap {X Y : Scheme.{u}} (g : X ⟶ Y) :
    baseProductFunctor (specULiftZIsTerminal.from X) ⟶
      baseProductFunctor (specULiftZIsTerminal.from Y) :=
  baseProductTransformation _ _ g (specULiftZIsTerminal.hom_ext _ _)

/-- Product maps preserve the actual commutative square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliarySupportMaps.lean:34"
  "adaptation" "Original actual open-pair maps, unchanged support and chosen zero."]
theorem productMap_square {A B : Scheme.OpenPairs.{u}} (g : A ⟶ B) (S : Scheme.{u}) :
    (productMap g.left).app S ≫
        (GlobalSupportedParameter.openTransformation B.hom).app S =
      (GlobalSupportedParameter.openTransformation A.hom).app S ≫
        (productMap g.right).app S := by
  dsimp only [productMap, GlobalSupportedParameter.openTransformation,
    baseProductTransformation, baseProductFunctor]
  apply pullback.hom_ext <;> simp [Category.assoc]

/-- An original open-pair square acts at every genuine scheme parameter. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliarySupportMaps.lean:44"
  "adaptation" "Original actual open-pair maps, unchanged support and chosen zero."]
def pairTransformation {A B : Scheme.OpenPairs.{u}} (g : A ⟶ B) :
    GlobalSupportedParameter.pairs A.hom ⟶
      GlobalSupportedParameter.pairs B.hom where
  app S := MorphismProperty.Arrow.homMk
    ((productMap g.left).app S) ((productMap g.right).app S)
    (productMap_square g S)
  naturality S T h := by
    apply MorphismProperty.Arrow.Hom.ext
    · exact (productMap g.left).naturality h
    · exact (productMap g.right).naturality h

/-- The supported map is the original exact open-pair pullback. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliarySupportMaps.lean:57"
  "adaptation" "Original actual open-pair maps, unchanged support and chosen zero."]
def supportedMap {A B : Scheme.OpenPairs.{u}} (g : A ⟶ B) :
    ParameterModels.supported B.hom ⟶ ParameterModels.supported A.hom :=
  Functor.whiskerRight (NatTrans.op (pairTransformation g)) pairSupported

/-- The ambient map uses the same original product pullback. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliarySupportMaps.lean:62"
  "adaptation" "Original actual open-pair maps, unchanged support and chosen zero."]
def ambientMap {X Y : Scheme.{u}} (g : X ⟶ Y) :
    ParameterModels.ambient Y ⟶ ParameterModels.ambient X :=
  Functor.whiskerRight (NatTrans.op (productMap g)) boundedAboveFlatGlobalSectionModelFunctor

/-- Every supported component retains the literal original underlying functor. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliarySupportMaps.lean:67"
  "adaptation" "Original actual open-pair maps, unchanged support and chosen zero."]
theorem supportedMap_functor {A B : Scheme.OpenPairs.{u}} (g : A ⟶ B)
    (S : Scheme.{u}ᵒᵖ) :
    ((supportedMap g).app S).hom.toFunctor =
      boundedAboveFlatGlobalSupportedPairReindex ((pairTransformation g).app S.unop) := rfl

/-- The existing selected supported zero is preserved, with no new zero choice. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliarySupportMaps.lean:73"
  "adaptation" "Original actual open-pair maps, unchanged support and chosen zero."]
theorem supportedMap_zero {A B : Scheme.OpenPairs.{u}} (g : A ⟶ B)
    (S : Scheme.{u}ᵒᵖ) :
    ((supportedMap g).app S).hom.toFunctor.obj
        ((ParameterModels.supported B.hom).obj S).obj.waldhausen.zero =
      ((ParameterModels.supported A.hom).obj S).obj.waldhausen.zero :=
  ((supportedMap g).app S).property

/-- Forgetting support retains the full original product pullback square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliarySupportMaps.lean:81"
  "adaptation" "Original actual open-pair maps, unchanged support and chosen zero."]
theorem supportedMap_forget {A B : Scheme.OpenPairs.{u}} (g : A ⟶ B) :
    supportedMap g ≫ ParameterModels.forget A.hom =
      ParameterModels.forget B.hom ≫ ambientMap g.right := by
  apply NatTrans.ext
  funext S
  exact boundedAboveFlatGlobalSupportedPairModelMap_forget ((pairTransformation g).app S.unop)

variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)

/-- The source acyclicity open is the original union. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliarySupportMaps.lean:91"
  "adaptation" "Original actual open-pair maps, unchanged support and chosen zero."]
abbrev unionOpen : Q.Opens := T ⊔ f.opensRange

/-- The target acyclicity open is the literal inverse image. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliarySupportMaps.lean:94"
  "adaptation" "Original actual open-pair maps, unchanged support and chosen zero."]
abbrev inverseOpen : P.Opens := f ⁻¹ᵁ T

/-- Original sections vanishing on the union, not a homotopy-fiber definition. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliarySupportMaps.lean:97"
  "adaptation" "Original actual open-pair maps, unchanged support and chosen zero."]
abbrev fiber : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{u + 1} :=
  ParameterModels.supported (unionOpen f T).ι

/-- Original sections with the auxiliary closed support. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliarySupportMaps.lean:101"
  "adaptation" "Original actual open-pair maps, unchanged support and chosen zero."]
abbrev ambient : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{u + 1} :=
  ParameterModels.supported T.ι

/-- Original fine supported sections on the open scheme. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliarySupportMaps.lean:105"
  "adaptation" "Original actual open-pair maps, unchanged support and chosen zero."]
abbrev openModel : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{u + 1} :=
  ParameterModels.supported (inverseOpen f T).ι

/-- The actual inclusion of support opens has identity ambient leg. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliarySupportMaps.lean:109"
  "adaptation" "Original actual open-pair maps, unchanged support and chosen zero."]
def enlargementPair : supportOpenPair T ⟶ supportOpenPair (unionOpen f T) :=
  MorphismProperty.Arrow.homMk (Q.homOfLE (show T ≤ unionOpen f T from le_sup_left))
    (𝟙 Q) (by
      change Q.homOfLE _ ≫ (unionOpen f T).ι = T.ι ≫ 𝟙 Q
      simpa only [Category.comp_id] using Scheme.homOfLE_ι Q _)

/-- Forget only the extra vanishing on the localization open. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliarySupportMaps.lean:116"
  "adaptation" "Original actual open-pair maps, unchanged support and chosen zero."]
def enlargement : fiber f T ⟶ ambient T := by
  let h := supportedMap (enlargementPair f T)
  dsimp only [supportOpenPair] at h
  exact h

/-- Restrict the original auxiliary-supported sections to the actual open scheme. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliarySupportMaps.lean:122"
  "adaptation" "Original actual open-pair maps, unchanged support and chosen zero."]
def restriction : ambient T ⟶ openModel f T := by
  let h := supportedMap (supportRestrictionPair f T)
  dsimp only [supportOpenPair] at h
  exact h

/-- The enlargement's ambient product pullback is literally identity. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliarySupportMaps.lean:128"
  "adaptation" "Original actual open-pair maps, unchanged support and chosen zero."]
theorem ambientMap_id (X : Scheme.{u}) : ambientMap (𝟙 X) = 𝟙 (ParameterModels.ambient X) := by
  have h : productMap (𝟙 X) = 𝟙 (baseProductFunctor (specULiftZIsTerminal.from X)) := by
    apply NatTrans.ext
    funext S
    apply pullback.hom_ext <;> simp [productMap, baseProductTransformation, baseProductFunctor]
  simp [ambientMap, h, ParameterModels.ambient]

/-- Support enlargement followed by forgetting is the original union-support forgetting. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliarySupportMaps.lean:136"
  "adaptation" "Original actual open-pair maps, unchanged support and chosen zero."]
theorem enlargement_forget :
    enlargement f T ≫ ParameterModels.forget T.ι =
      ParameterModels.forget (unionOpen f T).ι := by
  have h := supportedMap_forget (enlargementPair f T)
  change enlargement f T ≫ ParameterModels.forget T.ι =
    ParameterModels.forget (unionOpen f T).ι ≫ ambientMap (𝟙 Q) at h
  simpa only [ambientMap_id, Category.comp_id] using h

omit [IsOpenImmersion f] in
/-- Supported restriction and original ambient restriction commute strictly. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliarySupportMaps.lean:146"
  "adaptation" "Original actual open-pair maps, unchanged support and chosen zero."]
theorem restriction_forget :
    restriction f T ≫ ParameterModels.forget (inverseOpen f T).ι =
      ParameterModels.forget T.ι ≫ ambientMap f :=
  supportedMap_forget (supportRestrictionPair f T)

end ParameterAuxiliarySupport
end AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
