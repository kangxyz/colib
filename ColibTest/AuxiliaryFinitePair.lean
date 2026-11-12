/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.AuxiliaryFinitePair

/-! # Original section model and common-stage full-zero regression -/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Morphisms
open Scheme.Modules Stacks.AlgebraicGeometry.ModuleLimits
universe u
namespace AuxiliaryFinitePairRegression

local instance {X : Scheme.{u}} (M : X.Modules)
    [hM : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M] :
    Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M :=
  Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hM

local instance {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    [hM : SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M] :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property ((Scheme.Modules.pullback f).obj M) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom M hM

local instance {X : Scheme.{u}} (M N : X.Modules)
    [hM : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    [hN : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N] (z : Bool) :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (auxiliaryPairModules M N z) := by
  cases z
  · exact hN
  · exact (Stacks.SheafOfModules.isInvertible_tensorSheaf
      X.sheaf.obj X.ringCatSheaf.property M N).toAlgebraicGeometry

example
    {I : Type u} [Category.{u} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D C : I ⥤ Scheme.{u})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (C.map f)]
    [∀ i, IsNoetherian (D.obj i)] [∀ i, IsNoetherian (C.obj i)]
    (d : Cone D) (hd : IsLimit d) (c : Cone C) (hc : IsLimit c)
    (q : C ⟶ D) [∀ i, LocallyOfFiniteType (q.app i)] (qLimit : c.pt ⟶ d.pt)
    (hLimit : ∀ i, IsPullback (c.π.app i) qLimit (q.app i) (d.π.app i))
    (hcart : ∀ {i j} (f : j ⟶ i), IsPullback (C.map f) (q.app j) (q.app i) (D.map f))
    (i : I) (L : (C.obj i).Modules)
    [SheafOfModules.IsInvertible (C.obj i).sheaf.obj (C.obj i).ringCatSheaf.property L]
    (M N : c.pt.Modules)
    [SheafOfModules.IsInvertible c.pt.sheaf.obj c.pt.ringCatSheaf.property M]
    [hN : SheafOfModules.IsInvertible c.pt.sheaf.obj c.pt.ringCatSheaf.property N]
    (eM : M ≅ (Scheme.Modules.pullback (c.π.app i)).obj L)
    (a : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor c.pt.sheaf).obj M).obj N, ⊤))
    (b : Γ(N, ⊤))
    (hs : ∀ z, Stacks.Morphisms.IsFiniteLocallyFree
      ((zeroScheme c.pt (auxiliaryPairModules M N z) (auxiliaryPairSections M N a b z)).subschemeι ≫
        qLimit)) :
    ∃ (j : I) (e : j ⟶ i) (Nj : (C.obj j).Modules)
      (_hNj : SheafOfModules.IsInvertible (C.obj j).sheaf.obj (C.obj j).ringCatSheaf.property Nj)
      (eN : N ≅ (Scheme.Modules.pullback (c.π.app j)).obj Nj),
      let F := auxiliaryPairModules ((Scheme.Modules.pullback (C.map e)).obj L) Nj
      let E := auxiliaryPairModelIsos (c.π.app j) (C.map e) (c.π.app i) (c.w e) L Nj M N eM eN
      ∃ (k : I) (f : k ⟶ j) (t : ∀ z, Γ((Scheme.Modules.pullback (C.map f)).obj (F z), ⊤))
        (l : I) (g : l ⟶ k),
        (∀ z, Hom.app (canHom (c.π.app k) (C.map f) (c.π.app j) (c.w f) (F z)) ⊤
          (pullbackGlobalSections (c.π.app k) ((Scheme.Modules.pullback (C.map f)).obj (F z)) (t z)) =
            Hom.app (E z).hom ⊤ (auxiliaryPairSections M N a b z)) ∧
        ∀ z, Stacks.Morphisms.IsFiniteLocallyFree
          ((zeroScheme (C.obj l) ((Scheme.Modules.pullback (C.map g)).obj ((Scheme.Modules.pullback (C.map f)).obj (F z)))
            (pullbackGlobalSections (C.map g) ((Scheme.Modules.pullback (C.map f)).obj (F z)) (t z))).subschemeι ≫
              q.app l) ∧
          (zeroScheme (C.obj l) ((Scheme.Modules.pullback (C.map g)).obj ((Scheme.Modules.pullback (C.map f)).obj (F z)))
            (pullbackGlobalSections (C.map g) ((Scheme.Modules.pullback (C.map f)).obj (F z)) (t z))).comap
              (c.π.app l) =
            zeroScheme c.pt (auxiliaryPairModules M N z) (auxiliaryPairSections M N a b z) :=
  exists_original_auxiliaryFinitePair_of_isLimit D C d hd c hc q qLimit hLimit hcart i L M N eM a b hs

#print axioms AlgebraicGeometry.Scheme.Modules.exists_original_auxiliaryFinitePair_of_isLimit

end AuxiliaryFinitePairRegression
