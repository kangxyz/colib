/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Colib.AlgebraicGeometry.Modules.BoundedFlatGlobalSupportedPairModel
public import Colib.AlgebraicGeometry.Scheme.GlobalSupportedParameterGeometry

/-! # The original supported global section maps and strict diagram

These interfaces retain native global sections, their literal reindexing and the inherited
Stacks-perfect geometric fibers. They introduce no replacement perfect-complex model.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.SmallWaldhausenCategory
open AlgebraicGeometry.RingedSpace AlgebraicGeometry.Scheme.Products
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection

private theorem supported_lift_congr {C : Type*} [Category* C] {D : Type*} [Category* D]
    (P : ObjectProperty D) {F G : C ⥤ D} (h : F = G)
    (hF : ∀ x, P (F.obj x)) (hG : ∀ x, P (G.obj x)) : P.lift F hF = P.lift G hG := by
  subst h
  rfl


/-- The original ambient global Model on every open pair. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalSupportedPairDiagram.lean:23"
  "adaptation" "The original maps, support predicates and proof on native section data."]
def pairAmbient : Scheme.OpenPairs.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{u + 1} :=
  (MorphismProperty.Arrow.forget (@IsOpenImmersion : MorphismProperty Scheme.{u}) ⊤ ⊤ ⋙
    Arrow.rightFunc).op ⋙ boundedAboveFlatGlobalSectionModelFunctor

/-- Supported original global Models form a strict contravariant open-pair diagram. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalSupportedPairDiagram.lean:27"
  "adaptation" "The original maps, support predicates and proof on native section data."]
def pairSupported : Scheme.OpenPairs.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{u + 1} where
  obj A := boundedAboveFlatGlobalSupportedSectionModel (X := op A.unop.right) A.unop.hom
  map g := boundedAboveFlatGlobalSupportedPairModelMap g.unop
  map_id A := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    change (boundedAboveFlatGlobalSectionSupported (X := op A.unop.right) A.unop.hom).lift
      ((boundedAboveFlatGlobalSectionSupported (X := op A.unop.right) A.unop.hom).ι ⋙
        (boundedAboveFlatGlobalSectionModelFunctor.map (𝟙 (op A.unop.right))).hom.toFunctor) _ =
      (boundedAboveFlatGlobalSectionSupported (X := op A.unop.right) A.unop.hom).lift
        (boundedAboveFlatGlobalSectionSupported (X := op A.unop.right) A.unop.hom).ι _
    apply supported_lift_congr
    exact congrArg (fun F =>
      (boundedAboveFlatGlobalSectionSupported (X := op A.unop.right) A.unop.hom).ι ⋙ F)
      (congrArg (fun f => f.hom.toFunctor) (boundedAboveFlatGlobalSectionModelFunctor.map_id
        (op A.unop.right)))
  map_comp {A B C} g h := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    change (boundedAboveFlatGlobalSectionSupported (X := op C.unop.right) C.unop.hom).lift
      ((boundedAboveFlatGlobalSectionSupported (X := op A.unop.right) A.unop.hom).ι ⋙
        (boundedAboveFlatGlobalSectionModelFunctor.map (g.unop.right.op ≫
          h.unop.right.op)).hom.toFunctor) _ =
      (boundedAboveFlatGlobalSectionSupported (X := op C.unop.right) C.unop.hom).lift
        ((boundedAboveFlatGlobalSectionSupported (X := op A.unop.right) A.unop.hom).ι ⋙
          (boundedAboveFlatGlobalSectionModelFunctor.map g.unop.right.op).hom.toFunctor ⋙
          (boundedAboveFlatGlobalSectionModelFunctor.map h.unop.right.op).hom.toFunctor) _
    apply supported_lift_congr
    exact congrArg (fun F =>
      (boundedAboveFlatGlobalSectionSupported (X := op A.unop.right) A.unop.hom).ι ⋙ F)
      (congrArg (fun f => f.hom.toFunctor)
        (boundedAboveFlatGlobalSectionModelFunctor.map_comp g.unop.right.op h.unop.right.op))

/-- Forgetting support is a strict transformation of the original Model diagrams. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalSupportedPairDiagram.lean:56"
  "adaptation" "The original maps, support predicates and proof on native section data."]
def pairForget : pairSupported.{u} ⟶ pairAmbient where
  app A := boundedAboveFlatGlobalSupportedForget (X := op A.unop.right) A.unop.hom
  naturality _ _ g := boundedAboveFlatGlobalSupportedPairModelMap_forget g.unop

namespace ParameterModels
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The unchanged global ambient Model on the product with fixed right factor. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalSupportedPairDiagram.lean:64"
  "adaptation" "The original maps, support predicates and proof on native section data."]
def ambient (Q : Scheme.{u}) : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{u + 1} :=
  (baseProductFunctor (specULiftZIsTerminal.from Q)).op ⋙ boundedAboveFlatGlobalSectionModelFunctor

/-- The actual supported family for all scheme parameters, obtained by strict reindexing. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalSupportedPairDiagram.lean:68"
  "adaptation" "The original maps, support predicates and proof on native section data."]
def supported : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{u + 1} :=
  (GlobalSupportedParameter.pairs f).op ⋙ pairSupported

/-- The original support-forgetful map for every scheme parameter. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalSupportedPairDiagram.lean:72"
  "adaptation" "The original maps, support predicates and proof on native section data."]
def forget : supported f ⟶ ambient Q :=
  Functor.whiskerLeft (GlobalSupportedParameter.pairs f).op pairForget

end ParameterModels
end AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection

namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection

attribute [colib_tag "COL-0534"] pairSupported
attribute [colib_tag "COL-0534"] pairForget

end AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
