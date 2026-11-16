/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.GodementExactness
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.FlasqueExtensions
public import Colib.CategoryTheory.ExactCategory.Functor.Pushouts

/-! # The flasque resolution comparison for perfect K-theory

The original flasque and bounded below conditions select full subcategories of the same native
perfect complexes. Godement totalization and its augmentation yield inverse K-maps for the
literal inclusion into bounded below perfect complexes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory AlgebraicGeometry
open RingedSpaceModuleAdjunction
open scoped ZeroObject

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme.Modules.FlasquePerfect

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

variable {X : Scheme.{u}}

private def abSheaf (X : Scheme.{u}) : X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace)

private instance abSheaf_zero (X : Scheme.{u}) : (abSheaf X).PreservesZeroMorphisms :=
  ⟨fun _ _ => rfl⟩

private instance abSheaf_limits (X : Scheme.{u}) : PreservesFiniteLimits (abSheaf X) :=
  inferInstanceAs
    (PreservesFiniteLimits (SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace)))

private instance abSheaf_colimits (X : Scheme.{u}) : PreservesFiniteColimits (abSheaf X) :=
  inferInstanceAs
    (PreservesFiniteColimits (SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace)))

/-- Native perfect complexes with bounded below terms that are all flasque. -/
def objects (X : Scheme.{u}) : ObjectProperty (CochainComplex X.Modules ℤ) := fun K =>
  BoundedBelowPerfect.objects X K ∧ ∀ n, TopCat.Sheaf.IsFlasque
    ((SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace)).obj (K.X n))

/-- The full subcategory defined by the flasque and boundedness conditions. -/
abbrev Obj (X : Scheme.{u}) := (objects X).FullSubcategory

private theorem flasque_of_isZero {F : TopCat.Sheaf AddCommGrpCat.{u} (X : TopCat)}
    (hF : IsZero F) : F.IsFlasque where
  epi {U V} i := by
    have h : IsZero (F.obj.obj V) := by
      exact ((CategoryTheory.evaluation _ _).obj V).map_isZero
        ((TopCat.Sheaf.forget _ _).map_isZero hF)
    exact ⟨fun _ _ _ => h.eq_of_src _ _⟩

instance containsZero (X : Scheme.{u}) : (objects X).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, BoundedBelowPerfect.objects_of_isZero (isZero_zero _),
    fun n => flasque_of_isZero ((abSheaf X).map_isZero
      ((HomologicalComplex.eval X.Modules (ComplexShape.up ℤ) n).map_isZero (isZero_zero _)))⟩

instance closedUnderIso (X : Scheme.{u}) : (objects X).IsClosedUnderIsomorphisms where
  of_iso e hK := ⟨BoundedBelowPerfect.objects_of_iso e hK.1, fun n =>
    let ev := HomologicalComplex.eval X.Modules (ComplexShape.up ℤ) n
    TopCat.Sheaf.IsFlasque.of_iso ((abSheaf X).mapIso (ev.mapIso e).symm) (hK.2 n)⟩

instance extensionClosed (X : Scheme.{u}) :
    (abelianExactStructure (CochainComplex X.Modules ℤ)).IsExtensionClosed (objects X) where
  prop_middle {S} hS h₁ h₃ := by
    refine ⟨BoundedBelowPerfect.objects_of_shortExact hS h₁.1 h₃.1, fun n => ?_⟩
    let U := S.map (HomologicalComplex.eval X.Modules (ComplexShape.up ℤ) n)
    have hU : U.ShortExact := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS n
    let : (U.map (abSheaf X)).X₁.IsFlasque := h₁.2 n
    let : (U.map (abSheaf X)).X₃.IsFlasque := h₃.2 n
    exact TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₃ (hU.map_of_exact (abSheaf X))

instance closedUnderFiniteProducts (X : Scheme.{u}) : (objects X).IsClosedUnderFiniteProducts :=
  (abelianExactStructure (CochainComplex X.Modules ℤ)).extensionClosed_finiteProducts (objects X)

/-- The literal inclusion into the bounded below full subcategory. -/
def inclusion (X : Scheme.{u}) : Obj X ⥤ BoundedBelowPerfect.Obj X :=
  ObjectProperty.ιOfLE (fun _ h => h.1)

/-- The Waldhausen structure inherited by flasque perfect complexes. -/
def waldhausen (X : Scheme.{u}) : Waldhausen.Structure (Obj X) :=
  Waldhausen.complexSubcategory (objects X)

theorem inclusion_exact (X : Scheme.{u}) :
    Waldhausen.IsExact (waldhausen X).cof (waldhausen X).weq
      (BoundedBelowPerfect.waldhausen X).cof (BoundedBelowPerfect.waldhausen X).weq
      (inclusion X) :=
  Waldhausen.subcategoryInclusion_exact _ _ (fun _ h => h.1)

/-- The actual Godement total functor with its flasque target condition. -/
def total (X : Scheme.{u}) : BoundedBelowPerfect.Obj X ⥤ Obj X :=
  ObjectProperty.lift (objects X)
    (BoundedBelowPerfect.godementTotal X ⋙ (BoundedBelowPerfect.objects X).ι)
    (fun K => ⟨((BoundedBelowPerfect.godementTotal X).obj K).property,
      BoundedBelowPerfect.godementTotal_isFlasque K⟩)

instance total_additive (X : Scheme.{u}) : (total X).Additive where
  map_add {K L f g} := by
    apply ObjectProperty.hom_ext
    exact congrArg (fun m => m.hom)
      ((BoundedBelowPerfect.godementTotal X).map_add (f := f) (g := g))

/-- Godement totalization respects the inherited short exact sequences. -/
def totalExactFunctor (X : Scheme.{u}) : ExactFunctor
    (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex X.Modules ℤ))
      (BoundedBelowPerfect.objects X))
    (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex X.Modules ℤ))
      (objects X)) where
  toFunctor := total X
  map_conflation _ hS := BoundedBelowPerfect.godementTotal_shortExact hS

theorem total_exact (X : Scheme.{u}) :
    Waldhausen.IsExact (BoundedBelowPerfect.waldhausen X).cof
      (BoundedBelowPerfect.waldhausen X).weq (waldhausen X).cof (waldhausen X).weq (total X) where
  zero h := (total X).map_isZero h
  cofibration f hf := (totalExactFunctor X).map_inflation f hf
  weak f hf := BoundedBelowPerfect.godementTotal_map_quasiIso f hf
  pushout hi h := (totalExactFunctor X).map_isPushout hi h

/-- The Godement augmentation into the total followed by the literal inclusion. -/
def unit (X : Scheme.{u}) : 𝟭 (BoundedBelowPerfect.Obj X) ⟶ total X ⋙ inclusion X :=
  BoundedBelowPerfect.godementUnit X

/-- The same augmentation on a termwise flasque source. -/
def flasqueUnit (X : Scheme.{u}) : 𝟭 (Obj X) ⟶ inclusion X ⋙ total X where
  app K := ObjectProperty.homMk
    ((BoundedBelowPerfect.godementUnit X).app ((inclusion X).obj K)).hom
  naturality {K L} f := by
    apply ObjectProperty.hom_ext
    exact congrArg (fun m => m.hom)
      ((BoundedBelowPerfect.godementUnit X).naturality ((inclusion X).map f))

theorem unit_weak (X : Scheme.{u}) (K : BoundedBelowPerfect.Obj X) :
    (BoundedBelowPerfect.waldhausen X).weq ((unit X).app K) :=
  BoundedBelowPerfect.godementUnit_quasiIso K

theorem flasqueUnit_weak (X : Scheme.{u}) (K : Obj X) :
    (waldhausen X).weq ((flasqueUnit X).app K) :=
  BoundedBelowPerfect.godementUnit_quasiIso ((inclusion X).obj K)

end AlgebraicGeometry.Scheme.Modules.FlasquePerfect
