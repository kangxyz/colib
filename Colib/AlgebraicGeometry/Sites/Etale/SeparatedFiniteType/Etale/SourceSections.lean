/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Etale.Units

/-! # Actual full-small free-source sections and the units counit -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme Stacks.Cohomology.FreeYonedaUnivLE
universe u
private lemma equivalence_unit_map_counit {C D : Type*} [Category* C] [Category* D]
    (e : C ≌ D) {A : C} {H : D} (f : A ⟶ e.inverse.obj H) :
    e.unitIso.hom.app A ≫ e.inverse.map (e.functor.map f ≫ e.counitIso.hom.app H) = f := by
  rw [Functor.map_comp, ← Category.assoc]
  erw [← e.unitIso.hom.naturality f]
  simp

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {B : Scheme.{u}} [IsAffine B] (X : SmoothSite B)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The original free-source map transports every sheaf section through the actual basis unit. -/
lemma fullSmallSourceMap_sections (V : EtaleSeparatedFiniteType X.left)
    (G : Sheaf (SmoothSite.etaleTopology B) AddCommGrpCat.{u + 1})
    (f : (freeYoneda.{u + 1} (SmoothSite.etaleTopology B)).obj
      ((toSmoothSite X).obj V) ⟶ G) :
    sectionsEquiv.{u + 1} ((toSmallEtale X.left).obj V) ((fullSmallEtaleRestrict X).obj G)
      (fullSmallSourceMap X V ≫ (fullSmallEtaleRestrict X).map f) =
    (((sheafEquivSmallEtale X).unitIso.hom.app ((etaleRestrict X).obj G)).hom.app (op V))
      (sectionsEquiv.{u + 1} ((toSmoothSite X).obj V) G f) := by
  rw [sectionsEquiv_naturality]
  dsimp only [fullSmallSourceMap]
  rw [Equiv.apply_symm_apply, sectionsEquiv_eq_app_gen]
  have h := (sheafEquivSmallEtale X).unitIso.hom.naturality ((etaleRestrict X).map f)
  exact (congrArg (fun t => t.hom.app (op V)
    (gen.{u + 1} (J := SmoothSite.etaleTopology B) ((toSmoothSite X).obj V))) h).symm

/-- The actual full-small units iso cancels the basis-equivalence unit, by its counit law. -/
lemma fullSmallUnitsIso_unit :
    (sheafEquivSmallEtale X).unitIso.hom.app
        ((etaleRestrict X).obj (SmoothSite.largeUnitsEtaleSheaf B)) ≫
      (sheafEquivSmallEtale X).inverse.map (fullSmallUnitsIso X).hom =
        (basisUnitsIso X).hom := by
  exact equivalence_unit_map_counit (sheafEquivSmallEtale X) (basisUnitsIso X).hom

/-- The original restricted free-source map and units counit retain the actual unit section. -/
lemma fullSmallSourceMap_units (V : EtaleSeparatedFiniteType X.left)
    (f : (freeYoneda.{u + 1} (SmoothSite.etaleTopology B)).obj
      ((toSmoothSite X).obj V) ⟶ SmoothSite.largeUnitsEtaleSheaf B) :
    sectionsEquiv.{u + 1} ((toSmallEtale X.left).obj V)
      (Stacks.Kummer.multiplicativeSheaf.{u, 0} X.left)
      (fullSmallSourceMap X V ≫ (fullSmallEtaleRestrict X).map f ≫
        (fullSmallUnitsIso X).hom) =
    ULift.up (sectionsEquiv.{u + 1} ((toSmoothSite X).obj V)
      (SmoothSite.largeUnitsEtaleSheaf B) f).down := by
  rw [← Category.assoc, sectionsEquiv_naturality, fullSmallSourceMap_sections]
  have h := congrArg (fun t => t.hom.app (op V)
    (sectionsEquiv.{u + 1} ((toSmoothSite X).obj V)
      (SmoothSite.largeUnitsEtaleSheaf B) f)) (fullSmallUnitsIso_unit X)
  exact h

/-- At the original smooth object, the actual terminal-neighborhood source retains its unit. -/
lemma fullSmallSourceMapAtBase_units
    (f : (freeYoneda.{u + 1} (SmoothSite.etaleTopology B)).obj X ⟶
      SmoothSite.largeUnitsEtaleSheaf B) :
    let V : EtaleSeparatedFiniteType X.left :=
      MorphismProperty.Over.mk ⊤ (𝟙 X.left) (etaleSeparatedFiniteType.id_mem X.left)
    let g : (toSmoothSite X).obj V ⟶ X := SmoothSite.homMk (𝟙 X.left) (by rfl)
    sectionsEquiv.{u + 1} (Etale.mk (𝟙 X.left))
      (Stacks.Kummer.multiplicativeSheaf.{u, 0} X.left)
      ((freeYoneda.{u + 1} X.left.smallEtaleTopology).map
          (toSmallEtaleIdentityIso X.left).inv ≫
        fullSmallSourceMap X V ≫
          (fullSmallEtaleRestrict X).map
            ((freeYoneda.{u + 1} (SmoothSite.etaleTopology B)).map g ≫ f) ≫
          (fullSmallUnitsIso X).hom) =
      ULift.up (sectionsEquiv.{u + 1} X (SmoothSite.largeUnitsEtaleSheaf B) f).down := by
  dsimp only
  rw [sectionsEquiv_naturality_left, fullSmallSourceMap_units,
    sectionsEquiv_naturality_left]
  change ULift.up (Additive.ofMul
    (Units.map (𝟙 X.left : X.left ⟶ X.left).appTop.hom.toMonoidHom
      (Units.map (𝟙 X.left : X.left ⟶ X.left).appTop.hom.toMonoidHom
        (sectionsEquiv.{u + 1} X (SmoothSite.largeUnitsEtaleSheaf B) f).down.toMul))) = _
  simp
  rfl

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
