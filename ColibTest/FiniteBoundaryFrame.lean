module

import Colib.AlgebraicGeometry.Modules.Invertible.FiniteBoundaryFrame

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.SheafOfModules (IsInvertible)
open Stacks.SheafOfModules.Invertible

universe u v

local instance (S : Scheme.{v}) :
    ∀ U, IsMulCommutative ((ringSheaf S).obj.obj U) :=
  fun U => inferInstanceAs (IsMulCommutative (S.presheaf.obj U))

variable (R : Type u) [CommRing R] [StrictlyHenselianLocalRing R]
variable (B : Type v) [CommRing B] [Algebra R B] [Module.Finite R B]

-- The source of the frame is the original pulled-back sheaf, not its reduction.
example {C : Scheme.{v}} (i : Spec (CommRingCat.of B) ⟶ C) (L : C.Modules)
    [IsInvertible (Spec (CommRingCat.of B)).presheaf
      (ringSheafCond (Spec (CommRingCat.of B))) ((Scheme.Modules.pullback i).obj L)]
    (h6 : IsUnit (6 : R))
    (e : (Scheme.Modules.pullback i).obj L ≅
      SheafOfModules.unit (ringSheaf (Spec (CommRingCat.of B))))
    (α : tensorPower (Spec (CommRingCat.of B)).presheaf
      (ringSheafCond (Spec (CommRingCat.of B))) ((Scheme.Modules.pullback i).obj L) (6 : ℤ) ≅
        SheafOfModules.unit (ringSheaf (Spec (CommRingCat.of B)))) :
    ∃ e' : (Scheme.Modules.pullback i).obj L ≅
        SheafOfModules.unit (ringSheaf (Spec (CommRingCat.of B))),
      tensorPowerMap (Spec (CommRingCat.of B)) e' 6 ≪≫
        structureSheafTensorPowerIso (Spec (CommRingCat.of B)) 6 = α :=
  exists_pullback_frame_tensorPowerMap_eq_of_module_finite R B i L h6 e α

-- Exponent one and independent base/boundary universes are allowed.
example (L : SheafOfModules.{v} (ringSheaf (Spec (CommRingCat.of B))))
    [IsInvertible (Spec (CommRingCat.of B)).presheaf
      (ringSheafCond (Spec (CommRingCat.of B))) L]
    (e : L ≅ SheafOfModules.unit (ringSheaf (Spec (CommRingCat.of B))))
    (α : tensorPower (Spec (CommRingCat.of B)).presheaf
      (ringSheafCond (Spec (CommRingCat.of B))) L (1 : ℤ) ≅
        SheafOfModules.unit (ringSheaf (Spec (CommRingCat.of B)))) :
    ∃ e' : L ≅ SheafOfModules.unit (ringSheaf (Spec (CommRingCat.of B))),
      tensorPowerMap (Spec (CommRingCat.of B)) e' 1 ≪≫
        structureSheafTensorPowerIso (Spec (CommRingCat.of B)) 1 = α :=
  exists_frame_tensorPowerMap_eq_of_module_finite R B (by simp) L e α

-- The empty boundary is included: there is no Nontrivial B requirement.
example {n : ℕ} (hn : IsUnit (n : R))
    (α : tensorPower (Spec (CommRingCat.of PUnit.{v + 1})).presheaf
      (ringSheafCond (Spec (CommRingCat.of PUnit.{v + 1})))
      (SheafOfModules.unit (ringSheaf (Spec (CommRingCat.of PUnit.{v + 1})))) (n : ℤ) ≅
        SheafOfModules.unit (ringSheaf (Spec (CommRingCat.of PUnit.{v + 1})))) :
    ∃ e' : SheafOfModules.unit (ringSheaf (Spec (CommRingCat.of PUnit.{v + 1}))) ≅
        SheafOfModules.unit (ringSheaf (Spec (CommRingCat.of PUnit.{v + 1}))),
      tensorPowerMap (Spec (CommRingCat.of PUnit.{v + 1})) e' n ≪≫
        structureSheafTensorPowerIso (Spec (CommRingCat.of PUnit.{v + 1})) n = α :=
  exists_frame_tensorPowerMap_eq_of_module_finite R PUnit.{v + 1} hn _ (Iso.refl _) α

-- Semilocal triviality removes the initial frame for the actual boundary pullback.
example {C : Scheme.{v}} (i : Spec (CommRingCat.of B) ⟶ C) (L : C.Modules)
    [IsInvertible (Spec (CommRingCat.of B)).presheaf
      (ringSheafCond (Spec (CommRingCat.of B))) ((Scheme.Modules.pullback i).obj L)]
    (h6 : IsUnit (6 : R))
    (α : tensorPower (Spec (CommRingCat.of B)).presheaf
      (ringSheafCond (Spec (CommRingCat.of B))) ((Scheme.Modules.pullback i).obj L) (6 : ℤ) ≅
        SheafOfModules.unit (ringSheaf (Spec (CommRingCat.of B)))) :
    ∃ e : (Scheme.Modules.pullback i).obj L ≅
        SheafOfModules.unit (ringSheaf (Spec (CommRingCat.of B))),
      tensorPowerMap (Spec (CommRingCat.of B)) e 6 ≪≫
        structureSheafTensorPowerIso (Spec (CommRingCat.of B)) 6 = α :=
  exists_compatible_pullback_frame_of_module_finite R B i L h6 α

-- No initial frame and no nontriviality assumption, even for an arbitrary sheaf on Spec 0.
example {n : ℕ} (hn : IsUnit (n : R))
    (L : SheafOfModules.{v} (ringSheaf (Spec (CommRingCat.of PUnit.{v + 1}))))
    [IsInvertible (Spec (CommRingCat.of PUnit.{v + 1})).presheaf
      (ringSheafCond (Spec (CommRingCat.of PUnit.{v + 1}))) L]
    (α : tensorPower (Spec (CommRingCat.of PUnit.{v + 1})).presheaf
      (ringSheafCond (Spec (CommRingCat.of PUnit.{v + 1}))) L (n : ℤ) ≅
        SheafOfModules.unit (ringSheaf (Spec (CommRingCat.of PUnit.{v + 1})))) :
    ∃ e : L ≅ SheafOfModules.unit (ringSheaf (Spec (CommRingCat.of PUnit.{v + 1}))),
      tensorPowerMap (Spec (CommRingCat.of PUnit.{v + 1})) e n ≪≫
        structureSheafTensorPowerIso (Spec (CommRingCat.of PUnit.{v + 1})) n = α :=
  exists_compatible_frame_of_module_finite R PUnit.{v + 1} hn L α
