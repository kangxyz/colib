/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.AuxiliaryInvertibleModel
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.FiniteSectionModels

/-! # Original auxiliary numerator and denominator descend with their full zero schemes

The auxiliary module is selected after the fixed root model. Both original sections
are then descended together using their constructed tensor and auxiliary module
identifications, and one further stage makes both whole zero schemes finite locally free.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Morphisms
open Stacks.AlgebraicGeometry.ModuleLimits
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The two actual modules of a numerator and denominator, with the denominator
at `false` and the numerator at `true`. -/
def auxiliaryPairModules {X : Scheme.{u}} (M N : X.Modules) : Bool → X.Modules
  | false => N
  | true => ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).obj N

/-- Retain the original numerator and denominator sections as a finite family. -/
def auxiliaryPairSections {X : Scheme.{u}} (M N : X.Modules)
    (a : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).obj N, ⊤))
    (b : Γ(N, ⊤)) : ∀ z, Γ(auxiliaryPairModules M N z, ⊤)
  | false => b
  | true => a

local instance {X : Scheme.{u}} (M : X.Modules)
    [hM : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M] :
    Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M :=
  Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hM

local instance {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    [hM : SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M] :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property ((pullback f).obj M) :=
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

/-- The two module identifications are made from the original root and auxiliary
identifications; the numerator uses the actual canonical tensor comparison. -/
def auxiliaryPairModelIsos {W X Y : Scheme.{u}} (q : W ⟶ X) (g : X ⟶ Y)
    (p : W ⟶ Y) (hp : q ≫ g = p) (L : Y.Modules) (N : X.Modules)
    (M A : W.Modules) (eM : M ≅ (pullback p).obj L) (eA : A ≅ (pullback q).obj N) :
    ∀ z, auxiliaryPairModules M A z ≅
      (pullback q).obj (auxiliaryPairModules ((pullback g).obj L) N z)
  | false => eA
  | true => auxiliaryTensorModelIso q g p hp L N M A eM eA

/-- Starting with the original limit numerator and denominator, descend the
auxiliary module and both sections without reselecting the fixed original root model.
Both full zero schemes are finite locally free at the same final stage. -/
theorem exists_original_auxiliaryFinitePair_of_isLimit
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
    (eM : M ≅ (pullback (c.π.app i)).obj L)
    (a : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor c.pt.sheaf).obj M).obj N, ⊤))
    (b : Γ(N, ⊤))
    (hs : ∀ z, Stacks.Morphisms.IsFiniteLocallyFree
      ((zeroScheme c.pt (auxiliaryPairModules M N z) (auxiliaryPairSections M N a b z)).subschemeι ≫
        qLimit)) :
    ∃ (j : I) (e : j ⟶ i) (Nj : (C.obj j).Modules)
      (_hNj : SheafOfModules.IsInvertible (C.obj j).sheaf.obj (C.obj j).ringCatSheaf.property Nj)
      (eN : N ≅ (pullback (c.π.app j)).obj Nj),
      let F := auxiliaryPairModules ((pullback (C.map e)).obj L) Nj
      let E := auxiliaryPairModelIsos (c.π.app j) (C.map e) (c.π.app i) (c.w e) L Nj M N eM eN
      ∃ (k : I) (f : k ⟶ j) (t : ∀ z, Γ((pullback (C.map f)).obj (F z), ⊤))
        (l : I) (g : l ⟶ k),
        (∀ z, Hom.app (canHom (c.π.app k) (C.map f) (c.π.app j) (c.w f) (F z)) ⊤
          (pullbackGlobalSections (c.π.app k) ((pullback (C.map f)).obj (F z)) (t z)) =
            Hom.app (E z).hom ⊤ (auxiliaryPairSections M N a b z)) ∧
        ∀ z, Stacks.Morphisms.IsFiniteLocallyFree
          ((zeroScheme (C.obj l) ((pullback (C.map g)).obj ((pullback (C.map f)).obj (F z)))
            (pullbackGlobalSections (C.map g) ((pullback (C.map f)).obj (F z)) (t z))).subschemeι ≫
              q.app l) ∧
          (zeroScheme (C.obj l) ((pullback (C.map g)).obj ((pullback (C.map f)).obj (F z)))
            (pullbackGlobalSections (C.map g) ((pullback (C.map f)).obj (F z)) (t z))).comap
              (c.π.app l) =
            zeroScheme c.pt (auxiliaryPairModules M N z) (auxiliaryPairSections M N a b z) := by
  obtain ⟨j, e, Nj, hNj, eN, _⟩ :=
    exists_auxiliaryInvertible_tensorModel_of_isLimit C c hc i L M N eM hN
  let := hNj
  let F := auxiliaryPairModules ((pullback (C.map e)).obj L) Nj
  let E := auxiliaryPairModelIsos (c.π.app j) (C.map e) (c.π.app i) (c.w e) L Nj M N eM eN
  let (z : Bool) : (F z).IsFinitePresentation :=
    @AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isInvertible (C.obj j) (F z)
      (inferInstanceAs (SheafOfModules.IsInvertible (C.obj j).sheaf.obj
        (C.obj j).ringCatSheaf.property (auxiliaryPairModules ((pullback (C.map e)).obj L) Nj z)))
  exact ⟨j, e, Nj, hNj, eN,
    exists_originalSections_finiteLocallyFree_zeroSchemes_of_isLimit
      D C d hd c hc q qLimit hLimit hcart j F
      (auxiliaryPairModules M N) E (auxiliaryPairSections M N a b) hs⟩

end AlgebraicGeometry.Scheme.Modules
