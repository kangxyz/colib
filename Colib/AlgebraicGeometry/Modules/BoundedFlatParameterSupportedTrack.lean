/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatParameterLaurentUnit
public import Colib.AlgebraicGeometry.Modules.BoundedFlatGlobalSupportedPairDiagram
public import Colib.AlgebraicGeometry.Scheme.PolynomialLaurentCoefficient
public import Colib.KTheory.Bass.NaturalModelUnitTrack

/-!
# Original Laurent tracks on ambient and supported scheme-parameter sections

The actual support-forgetful transformation preserves the original scalar track at every time.
The relative-open category, change of weakness and geometric restriction are separate prerequisites;
this file does not assert their track comparisons or the final localization theorem.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Functor.IdentityAutomorphism
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open Topology.LoopPrespectrum KTheory.Bass
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterLaurentTrack
open GlobalSupportedSection GlobalSupportedParameter
open ParameterLaurentUnit NaturalTrack

private theorem preservesRestricted {C D : Type*} [Category C] [Category D]
    (P : ObjectProperty C) (Q : ObjectProperty D) (F : C ⥤ D)
    (hF : ∀ x : P.FullSubcategory, Q (F.obj x.obj))
    (α : 𝟭 C ≅ 𝟭 C) (β : 𝟭 D ≅ 𝟭 D) (h : Preserves F α β) :
    Preserves (Q.lift (P.ι ⋙ F) hF) (lift P.ι α) (lift Q.ι β) := by
  intro x
  apply ObjectProperty.hom_ext
  change F.map (((lift P.ι α).hom.app x).hom) =
    ((lift Q.ι β).hom.app ((Q.lift (P.ι ⋙ F) hF).obj x)).hom
  rw [show ((lift P.ι α).hom.app x).hom = α.hom.app x.obj from map_lift_hom P.ι α x,
    show ((lift Q.ι β).hom.app ((Q.lift (P.ι ⋙ F) hF).obj x)).hom =
      β.hom.app (F.obj x.obj) from map_lift_hom Q.ι β _]
  exact h x.obj

/-- The original whole ambient parameter track under every scheme morphism. -/
@[colib_ref "quillen" "Quillen c561118b: ParameterLaurentTrack.lean:53"
  "adaptation" "Original supported unit and complete-time realization on native sections."]
def ambientTrack (Q : Scheme.{u}) :
    Track laurent.op coefficient (ParameterModels.ambient Q ⋙ prespectrumFunctor) :=
  ofModelUnits laurent.op coefficient (ParameterModels.ambient Q)
    (ambientUnit Q) (ambientUnit_naturality Q)

variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The original support predicate on each actual parameter ambient category. -/
@[colib_ref "quillen" "Quillen c561118b: ParameterLaurentTrack.lean:61"
  "adaptation" "Original supported unit and complete-time realization on native sections."]
abbrev parameterSupported (X : Scheme.{u}ᵒᵖ) :
    ObjectProperty ((ParameterModels.ambient Q).obj X).obj.Obj :=
  boundedAboveFlatGlobalSectionSupported (X := op (pair f X.unop).right) (pair f X.unop).hom

/-- Restrict the same projected global unit to the actual supported full subcategory. -/
@[colib_ref "quillen" "Quillen c561118b: ParameterLaurentTrack.lean:66"
  "adaptation" "Original supported unit and complete-time realization on native sections."]
def supportedUnit (X : Scheme.{u}ᵒᵖ) :
    𝟭 (parameterSupported f (laurent.op.obj X)).FullSubcategory ≅
      𝟭 (parameterSupported f (laurent.op.obj X)).FullSubcategory :=
  lift (parameterSupported f (laurent.op.obj X)).ι (ambientUnit Q X)

/-- Original supported parameter pullback preserves the same lifted identity unit. -/
@[colib_ref "quillen" "Quillen c561118b: ParameterLaurentTrack.lean:72"
  "adaptation" "Original supported unit and complete-time realization on native sections."]
theorem supportedUnit_naturality {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) :
    Preserves ((ParameterModels.supported f).map (laurent.op.map g)).hom.toFunctor
      (supportedUnit f X) (supportedUnit f Y) :=
  preservesRestricted (parameterSupported f (laurent.op.obj X))
    (parameterSupported f (laurent.op.obj Y)) _
    (fun x => boundedAboveFlatGlobalPairReindex_supported
      (pairMap f (laurent.op.map g).unop) x.obj x.property)
    _ _ (ambientUnit_naturality Q g)

/-- The original whole supported parameter track, with no replacement of support by a fiber. -/
@[colib_ref "quillen" "Quillen c561118b: ParameterLaurentTrack.lean:81"
  "adaptation" "Original supported unit and complete-time realization on native sections."]
def supportedTrack :
    Track laurent.op coefficient (ParameterModels.supported f ⋙ prespectrumFunctor) :=
  ofModelUnits laurent.op coefficient (ParameterModels.supported f)
    (supportedUnit f) (supportedUnit_naturality f)

/-- Forgetting support preserves the actual lifted unit component. -/
@[colib_ref "quillen" "Quillen c561118b: ParameterLaurentTrack.lean:104"
  "adaptation" "Original supported unit and complete-time realization on native sections."]
theorem forget_unit (X : Scheme.{u}ᵒᵖ) :
    Preserves ((ParameterModels.forget f).app (laurent.op.obj X)).hom.toFunctor
      (supportedUnit f X) (ambientUnit Q X) := by
  have h : Preserves (parameterSupported f (laurent.op.obj X)).ι
      (lift (parameterSupported f (laurent.op.obj X)).ι (ambientUnit Q X))
      (ambientUnit Q X) := fun x =>
    map_lift_hom (parameterSupported f (laurent.op.obj X)).ι (ambientUnit Q X) x
  exact h

/-- Support forget preserves every time of the original parameter scalar track. -/
@[colib_ref "quillen" "Quillen c561118b: ParameterLaurentTrack.lean:125"
  "adaptation" "Original supported unit and complete-time realization on native sections."]
theorem forget_equivariant :
    Equivariant (supportedTrack f) (ambientTrack Q)
      (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor) :=
  ofModelUnits_equivariant _ _ _ _ _ _ _ _ _ (forget_unit f)

end AlgebraicGeometry.Scheme.Modules.ParameterLaurentTrack

namespace AlgebraicGeometry.Scheme.Modules.ParameterLaurentTrack

attribute [colib_tag "COL-0540"] forget_equivariant
attribute [colib_tag "COL-0540"] ambientTrack
attribute [colib_tag "COL-0540"] supportedTrack

end AlgebraicGeometry.Scheme.Modules.ParameterLaurentTrack
