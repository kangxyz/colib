/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.FlasqueResolution
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.FlasquePushforward

/-! # The actual direct-image functor on flasque perfect complexes

Termwise direct image lands in the canonical native perfect complexes under the proper-flat
hypotheses. On the flasque source it respects the inherited short exact sequences and genuine
quasi-isomorphisms, so induces the actual Waldhausen K-map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open AlgebraicGeometry AlgebraicGeometry.RingedSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme.Modules.FlasquePerfect

universe u

attribute [local instance] Abelian.hasFiniteBiproducts
attribute [local instance 2000] HasDerivedCategory.standard

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

local notation "P" => (IsPerfectComplex
  (X := LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace Y)))
local notation "F" => (Functor.mapHomologicalComplex (pushforward f) (ComplexShape.up ℤ))

variable [Flat f] [IsProper f] [LocallyOfFinitePresentation f]

/-- The literal direct image of bounded below termwise flasque perfect complexes. -/
def perfectPushforward : Obj X ⥤ ObjectProperty.FullSubcategory P :=
  ObjectProperty.lift P ((objects X).ι ⋙ F)
    (fun K => isPerfectComplex_flasquePushforward f K.obj K.property.1.1
      K.property.1.2 K.property.2)

instance perfectPushforward_additive : (perfectPushforward f).Additive where
  map_add {K L g h} := by
    apply ObjectProperty.hom_ext
    exact (F).map_add (f := g.hom) (g := h.hom)

/-- The actual direct image preserves inherited short exact sequences on flasque objects. -/
theorem perfectPushforward_shortExact {S : ShortComplex (Obj X)}
    (hS : (S.map (objects X).ι).ShortExact) :
    ((S.map (perfectPushforward f)).map (ObjectProperty.ι P)).ShortExact := by
  let U := S.map (objects X).ι
  change (U.map (F)).ShortExact
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let T := U.map (HomologicalComplex.eval X.Modules (ComplexShape.up ℤ) n)
  change (T.map (pushforward f)).ShortExact
  exact pushforward_shortExact_of_flasque f T (hS.map_of_exact _)
    (S.X₁.property.2 n) (S.X₂.property.2 n)

private theorem pushforward_quasiIso {K L : Obj X} (g : K ⟶ L) (hg : QuasiIso g.hom) :
    QuasiIso ((perfectPushforward f).map g).hom := by
  let qX := HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)
  let qY := HomotopyCategory.quotient Y.Modules (ComplexShape.up ℤ)
  let QhX := DerivedCategory.Qh (C := X.Modules)
  let QhY := DerivedCategory.Qh (C := Y.Modules)
  let α := derivedPushforwardModulesUnit f
  let R := derivedPushforwardModules f
  have hq : IsIso (QhX.map (qX.map g.hom)) := by
    let : IsIso (DerivedCategory.Q.map g.hom) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso X.Modules g.hom).2 hg
    let : IsIso (QhX.map (qX.map g.hom) ≫
        (DerivedCategory.quotientCompQhIso X.Modules).hom.app L.obj) := by
      rw [DerivedCategory.quotientCompQhIso_hom_naturality]
      infer_instance
    exact IsIso.of_isIso_comp_right (QhX.map (qX.map g.hom))
      ((DerivedCategory.quotientCompQhIso X.Modules).hom.app L.obj)
  let : IsIso (α.app (qX.obj K.obj)) :=
    isIso_flasquePushforwardUnit_app f K.obj K.property.1.2 K.property.2
  let : IsIso (α.app (qX.obj L.obj)) :=
    isIso_flasquePushforwardUnit_app f L.obj L.property.1.2 L.property.2
  let H := (pushforward f).mapHomotopyCategory (ComplexShape.up ℤ)
  let e := (pushforward f).mapHomotopyCategoryFactors (ComplexShape.up ℤ)
  have hH : IsIso (QhY.map (H.map (qX.map g.hom))) := by
    let : IsIso (QhY.map (H.map (qX.map g.hom)) ≫ α.app (qX.obj L.obj)) := by
      change IsIso ((H ⋙ QhY).map (qX.map g.hom) ≫ α.app (qX.obj L.obj))
      rw [α.naturality]
      change IsIso (α.app (qX.obj K.obj) ≫ R.map (QhX.map (qX.map g.hom)))
      infer_instance
    exact IsIso.of_isIso_comp_right (QhY.map (H.map (qX.map g.hom)))
      (α.app (qX.obj L.obj))
  have hn : QhY.map (H.map (qX.map g.hom)) ≫ QhY.map (e.hom.app L.obj) =
      QhY.map (e.hom.app K.obj) ≫ QhY.map (qY.map ((F).map g.hom)) := by
    have h := e.hom.naturality g.hom
    simp only [Functor.comp_map] at h
    simpa only [← Functor.map_comp] using congrArg QhY.map h
  let : IsIso (QhY.map (e.hom.app K.obj) ≫ QhY.map (qY.map ((F).map g.hom))) := by
    rw [← hn]
    infer_instance
  let : IsIso (QhY.map (qY.map ((F).map g.hom))) :=
    IsIso.of_isIso_comp_left (QhY.map (e.hom.app K.obj)) (QhY.map (qY.map ((F).map g.hom)))
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso Y.Modules _).1
  change IsIso (DerivedCategory.Q.map ((F).map g.hom))
  let : IsIso ((DerivedCategory.quotientCompQhIso Y.Modules).hom.app ((F).obj K.obj) ≫
      DerivedCategory.Q.map ((F).map g.hom)) := by
    rw [← DerivedCategory.quotientCompQhIso_hom_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((DerivedCategory.quotientCompQhIso Y.Modules).hom.app ((F).obj K.obj))
    (DerivedCategory.Q.map ((F).map g.hom))

/-- Actual direct image is Waldhausen exact on the termwise flasque source. -/
theorem perfectPushforward_exact :
    Waldhausen.IsExact (waldhausen X).cof (waldhausen X).weq
      (perfectComplexesWaldhausen Y.toRingedSpace).cof
      (perfectComplexesWaldhausen Y.toRingedSpace).weq (perfectPushforward f) := by
  let E : ExactFunctor
      (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex X.Modules ℤ))
        (objects X))
      (abelianExactStructure (CochainComplex Y.Modules ℤ)) :=
    { toFunctor := perfectPushforward f ⋙ ObjectProperty.ι P
      map_conflation := fun _ hS => perfectPushforward_shortExact f hS }
  refine { zero := fun h => (perfectPushforward f).map_isZero h
           cofibration := ?_
           weak := pushforward_quasiIso f
           pushout := ?_ }
  · intro K L g hg
    exact (abelianExactStructure_inflation_iff _ _).1 (E.map_inflation g hg)
  · intro A B C D i g h j hi hp
    apply IsPushout.of_map_of_faithful (ObjectProperty.ι P)
    exact E.map_isPushout hi hp

end AlgebraicGeometry.Scheme.Modules.FlasquePerfect
