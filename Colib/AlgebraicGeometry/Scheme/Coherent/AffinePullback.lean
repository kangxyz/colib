/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.Coherent.AffineEquivalence
public import Colib.AlgebraicGeometry.Scheme.Coherent.Pullback
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde

/-!
# Actual sections of affine coherent pullback

The original tilde counit and Stacks' native affine pullback/extension-of-scalars
isomorphism identify global sections of coherent pullback with actual tensor
extension. This ordinary functor comparison does not assume flatness.

Implementation source: the ordinary comparison in
`Quillen/AlgebraicGeometry/Scheme/Coherent/Affine/LocalizationNaturality.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules.Coherent
variable (R : CommRingCat.{u}) [IsNoetherianRing R]

/-- The original affine counit, after the literal inclusion of native coherent sheaves. -/
def coherentTildeCounitIso :
    (affineGlobalSections R ⋙ forget₂ (FGModuleCat R) (ModuleCat R)) ⋙ tilde.functor R ≅
      ObjectProperty.ι (fun M : (Spec R).Modules => M.IsCoherent) :=
  Functor.isoWhiskerRight (affineEquivalence R).counitIso (ObjectProperty.ι _)

variable {R} {T : CommRingCat.{u}} [IsNoetherianRing T] (φ : R ⟶ T)

/-- Original coherent pullback identifies its actual sections with scalar extension. -/
def coherentPullbackGlobalSectionsExtensionIso :
    coherentPullback (Spec.map φ) ⋙ affineGlobalSections T ⋙
        forget₂ (FGModuleCat T) (ModuleCat T) ≅
      affineGlobalSections R ⋙ forget₂ (FGModuleCat R) (ModuleCat R) ⋙
        ModuleCat.extendScalars φ.hom := by
  let Γ := affineGlobalSections R ⋙ forget₂ (FGModuleCat R) (ModuleCat R)
  let e₁ : Γ ⋙ tilde.functor R ≅
      ObjectProperty.ι (fun M : (Spec R).Modules => M.IsCoherent) :=
    coherentTildeCounitIso R
  let e₂ := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft Γ (pullbackTildeIso R T φ)) (moduleSpecΓFunctor (R := T))
  let e₃ := Functor.isoWhiskerLeft (Γ ⋙ ModuleCat.extendScalars φ.hom)
    (tilde.toTildeΓNatIso (R := T)).symm
  exact Functor.isoWhiskerRight e₁.symm
      (Scheme.Modules.pullback (Spec.map φ) ⋙ moduleSpecΓFunctor (R := T)) ≪≫ e₂ ≪≫ e₃

end AlgebraicGeometry.Scheme.Modules.Coherent
