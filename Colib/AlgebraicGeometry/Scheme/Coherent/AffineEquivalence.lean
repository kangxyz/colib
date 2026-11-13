/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.Coherent.Exact
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleTypesUnderEquivalence

/-!
# Native coherent sheaves on an affine scheme

Over a Noetherian ring, the actual tilde and global-sections functors restrict
to finite modules and the existing native coherent sheaf category. The units
and counits are the original affine adjunction maps. No alternate coherent
category or module-carrier model is introduced.

This supplies the native replacement for the affine equivalence used by
`Quillen/AlgebraicGeometry/Scheme/Coherent/Affine/GTheory.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.CoherentOfFiniteType
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules.Coherent
variable (R : CommRingCat.{u}) [IsNoetherianRing R]

/-- Tilde carries a finite module to the existing native coherent sheaf category. -/
def affineTilde : FGModuleCat.{u} R ⥤ SheafOfModules.CoherentModules (Spec R).ringCatSheaf :=
  ObjectProperty.lift _ (forget₂ (FGModuleCat R) (ModuleCat R) ⋙ tilde.functor R) (by
    intro M
    have : Module.Finite R M.obj := M.property
    have : (tilde M.obj).IsFiniteType := (tilde_isFiniteType_iff M.obj).2 inferInstance
    exact isCoherent_of_isQuasicoherent_of_isFiniteType
      (tilde M.obj))

omit [IsNoetherianRing R] in
/-- Actual affine global sections of a coherent sheaf are finite over the base ring. -/
theorem finite_affineGlobalSections
    (M : SheafOfModules.CoherentModules (Spec R).ringCatSheaf) :
    Module.Finite R (moduleSpecΓFunctor.obj M.obj) := by
  have : M.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent M.obj
  have : M.obj.IsFiniteType :=
    @_root_.SheafOfModules.IsCoherent.isFiniteType _ _ _ M.obj M.property
  have h : (tilde (moduleSpecΓFunctor.obj M.obj)).IsFiniteType :=
    Stacks.SheafOfModules.Intrinsic.isFiniteType_of_iso.{u, u, u}
      (asIso (Scheme.Modules.fromTildeΓ M.obj)).symm inferInstance
  exact (tilde_isFiniteType_iff _).1 h

omit [IsNoetherianRing R] in
/-- The literal affine global-sections functor restricted to native coherent sheaves. -/
def affineGlobalSections :
    SheafOfModules.CoherentModules (Spec R).ringCatSheaf ⥤ FGModuleCat.{u} R :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ moduleSpecΓFunctor)
    (finite_affineGlobalSections R)

/-- The original tilde/global-sections adjunction restricts to a native equivalence. -/
def affineEquivalence :
    FGModuleCat.{u} R ≌ SheafOfModules.CoherentModules (Spec R).ringCatSheaf where
  functor := affineTilde R
  inverse := affineGlobalSections R
  unitIso := NatIso.ofComponents
    (fun M => ObjectProperty.isoMk _ (tilde.toTildeΓNatIso.app M.obj)) (by
      intro M N f
      apply ObjectProperty.hom_ext
      exact tilde.toTildeΓNatIso.hom.naturality f.hom)
  counitIso :=
    haveI (M : SheafOfModules.CoherentModules (Spec R).ringCatSheaf) :
        M.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent M.obj
    NatIso.ofComponents
    (fun M => by
      haveI : IsIso (Scheme.Modules.fromTildeΓ M.obj) :=
        Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := R) M.obj
      exact ObjectProperty.isoMk _ (asIso (Scheme.Modules.fromTildeΓ M.obj))) (by
      intro M N f
      apply ObjectProperty.hom_ext
      exact (tilde.adjunction (R := R)).counit.naturality f.hom)
  functor_unitIso_comp M := by
    apply ObjectProperty.hom_ext
    exact (tilde.adjunction (R := R)).left_triangle_components M.obj

instance affineTilde_isEquivalence : (affineTilde R).IsEquivalence :=
  (affineEquivalence R).isEquivalence_functor

instance affineGlobalSections_isEquivalence : (affineGlobalSections R).IsEquivalence :=
  (affineEquivalence R).isEquivalence_inverse

instance affineTilde_additive : (affineTilde R).Additive :=
  Functor.additive_of_preserves_binary_products _

instance affineGlobalSections_additive : (affineGlobalSections R).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Tilde is exact for the native abelian exact structures. -/
def affineTildeExact : CategoryTheory.ExactCategory.ExactFunctor
    (CategoryTheory.ExactCategory.abelianExactStructure (FGModuleCat.{u} R))
    (coherentExactStructure (Spec R)) where
  toFunctor := affineTilde R
  map_conflation _ h := h.map_of_exact _

/-- Actual affine global sections are exact on the native coherent category. -/
def affineGlobalSectionsExact : CategoryTheory.ExactCategory.ExactFunctor
    (coherentExactStructure (Spec R))
    (CategoryTheory.ExactCategory.abelianExactStructure (FGModuleCat.{u} R)) where
  toFunctor := affineGlobalSections R
  map_conflation _ h := h.map_of_exact _

end AlgebraicGeometry.Scheme.Modules.Coherent
