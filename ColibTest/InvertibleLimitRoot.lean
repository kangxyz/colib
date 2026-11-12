module

import Colib.AlgebraicGeometry.Modules.Invertible.LimitRoot
import StacksFrontier.AlgebraicGeometry.PicardGroup.TensorPower

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits Stacks.SheafOfModules.Invertible

universe u

local instance (X : Scheme.{u}) (L : X.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
  Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL

-- Consume the result as an actual square root at one stage over the originally specified
-- target stage. There is no stage-root, continuity, or reducedness premise.
example {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D) (hc : IsLimit c)
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (i : I) (L : (D.obj i).Modules) [L.IsFinitePresentation] (M : c.pt.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible c.pt.sheaf.obj c.pt.ringCatSheaf.property M]
    (α : tensorPower c.pt.sheaf.obj c.pt.ringCatSheaf.property M (2 : ℤ) ≅
      (Scheme.Modules.pullback (c.π.app i)).obj L) :
    ∃ (j : I) (e : j ⟶ i) (Mj : (D.obj j).Modules)
      (hMj : AlgebraicGeometry.SheafOfModules.IsInvertible
        (D.obj j).sheaf.obj (D.obj j).ringCatSheaf.property Mj),
      let _ := hMj
      Nonempty (tensorPower (D.obj j).sheaf.obj (D.obj j).ringCatSheaf.property Mj (2 : ℤ) ≅
        (Scheme.Modules.pullback (D.map e)).obj L) :=
  exists_tensorPower_root_pullback_iso_of_isLimit D c hc i L M 2 α

-- The root supplied by the existing Picard/Kummer interface is the same native tensor-power
-- object, so its actual isomorphism can be used without replacing the chosen root.
example {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D) (hc : IsLimit c)
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (i : I) (L : (D.obj i).Modules) [L.IsFinitePresentation] (M : c.pt.Modules)
    (hM : Stacks.SheafOfModules.IsInvertible c.pt.presheaf c.pt.ringCatIsSheaf M)
    (α : Stacks.SheafOfModules.schemeTensorPower c.pt M hM (2 : ℤ) ≅
      (Scheme.Modules.pullback (c.π.app i)).obj L) :
    ∃ (j : I) (e : j ⟶ i) (Mj : (D.obj j).Modules)
      (hMj : AlgebraicGeometry.SheafOfModules.IsInvertible
        (D.obj j).sheaf.obj (D.obj j).ringCatSheaf.property Mj),
      let _ := hMj
      Nonempty (tensorPower (D.obj j).sheaf.obj (D.obj j).ringCatSheaf.property Mj (2 : ℤ) ≅
        (Scheme.Modules.pullback (D.map e)).obj L) := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible
      c.pt.sheaf.obj c.pt.ringCatSheaf.property M :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hM
  exact exists_tensorPower_root_pullback_iso_of_isLimit D c hc i L M 2 α
