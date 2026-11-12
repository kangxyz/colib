module

import Colib.AlgebraicGeometry.Modules.Limits.TensorPowerIsomorphisms

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits Stacks.SheafOfModules.Invertible

universe u

-- Two power equations and two prescribed sections hold for the same original transition.
example {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] (i : I) (A B : (D.obj i).Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible (D.obj i).toRingedSpace.presheaf
      (structureSheafRing (D.obj i).toRingedSpace).property A]
    [AlgebraicGeometry.SheafOfModules.IsInvertible (D.obj i).toRingedSpace.presheaf
      (structureSheafRing (D.obj i).toRingedSpace).property B]
    (N : (Scheme.Modules.pullback (c.π.app i)).obj A ≅
      (Scheme.Modules.pullback (c.π.app i)).obj B)
    (n : Fin 2 → ℕ)
    (α : ∀ x, tensorPower (D.obj i).toRingedSpace.presheaf
        (structureSheafRing (D.obj i).toRingedSpace).property A (n x : ℤ) ⟶
      tensorPower (D.obj i).toRingedSpace.presheaf
        (structureSheafRing (D.obj i).toRingedSpace).property B (n x : ℤ))
    (hα : ∀ x, (pullbackPowerIso (c.π.app i) A B N (n x)).hom =
      (Scheme.Modules.pullback (c.π.app i)).map (α x))
    (s : Fin 2 → (SheafOfModules.unit (D.obj i).ringCatSheaf ⟶ A))
    (t : Fin 2 → (SheafOfModules.unit (D.obj i).ringCatSheaf ⟶ B))
    (hst : ∀ x, (Scheme.Modules.pullback (c.π.app i)).map (s x) ≫ N.hom =
      (Scheme.Modules.pullback (c.π.app i)).map (t x)) :
    ∃ (j : I) (f : j ⟶ i)
      (m : (Scheme.Modules.pullback (D.map f)).obj A ≅
        (Scheme.Modules.pullback (D.map f)).obj B),
      ((Scheme.Modules.pullback (c.π.app j)).map m.hom ≫
          canHom (c.π.app j) (D.map f) (c.π.app i) (c.w f) B =
        canHom (c.π.app j) (D.map f) (c.π.app i) (c.w f) A ≫ N.hom) ∧
      (∀ x, (pullbackPowerIso (D.map f) A B m (n x)).hom =
        (Scheme.Modules.pullback (D.map f)).map (α x)) ∧
      ∀ x, (Scheme.Modules.pullback (D.map f)).map (s x) ≫ m.hom =
        (Scheme.Modules.pullback (D.map f)).map (t x) := by
  have : (SheafOfModules.unit (D.obj i).ringCatSheaf).IsFinitePresentation :=
    isFinitePresentation_unit _
  exact exists_iso_pullback_power_comp_eq_of_isLimit_finite D c hc i A B N n α hα
    (fun _ : Fin 2 => SheafOfModules.unit (D.obj i).ringCatSheaf) s t hst
