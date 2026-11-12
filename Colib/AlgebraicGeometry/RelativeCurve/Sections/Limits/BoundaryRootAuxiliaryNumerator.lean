/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Modules.Limits.BoundaryRoot
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.BoundaryScalarPullback
public import
  Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.AuxiliaryNumeratorDescentEquation

/-! # One stage for the specific root frame and actual auxiliary numerator

The root/frame finite consumer is fed the linear equation derived from the original
numerator and its full-boundary value. One refinement preserves the actual root
power, frame recovery, and numerator normalization together.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules Stacks.SheafOfModules.Invertible
universe u
namespace Stacks.AlgebraicGeometry.ModuleLimits

/-- The specified root frame and actual original numerator descend together to
one stage; the numerator equation is derived from its original boundary value. -/
theorem exists_boundary_root_frame_with_auxiliaryNumerator
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (B C : I ⥤ Scheme.{u}) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (B.map f)]
    (b : B ⟶ C) (cB : Limits.Cone B) (hcB : Limits.IsLimit cB)
    [∀ i, CompactSpace (B.obj i)] [∀ i, QuasiSeparatedSpace (B.obj i)]
    (cC : Limits.Cone C) (bLim : cB.pt ⟶ cC.pt)
    (hb : ∀ i, cB.π.app i ≫ b.app i = bLim ≫ cC.π.app i)
    (i : I) (M L : (C.obj i).Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible (C.obj i).toRingedSpace.presheaf
      (structureSheafRing (C.obj i).toRingedSpace).property M] (n : ℕ)
    (α : tensorPower (C.obj i).toRingedSpace.presheaf
      (structureSheafRing (C.obj i).toRingedSpace).property M (n : ℤ) ≅ L)
    (τ : (Scheme.Modules.pullback (b.app i)).obj L ≅
      SheafOfModules.unit (B.obj i).ringCatSheaf)
    (N : (C.obj i).Modules) (M₀ N₀ : cC.pt.Modules)
    (E : M₀ ≅ (Scheme.Modules.pullback (cC.π.app i)).obj M)
    (F : N₀ ≅ (Scheme.Modules.pullback (cC.π.app i)).obj N)
    (eM : (Scheme.Modules.pullback bLim).obj M₀ ≅ SheafOfModules.unit cB.pt.ringCatSheaf)
    (eN : (Scheme.Modules.pullback bLim).obj N₀ ≅ SheafOfModules.unit cB.pt.ringCatSheaf)
    (heLim : tensorPowerCongr cB.pt.toRingedSpace.presheaf
      (structureSheafRing cB.pt.toRingedSpace).property _ _ (((Scheme.Modules.pullback
        bLim).mapIso E).symm ≪≫ eM) n =
        boundaryRootPowerIso bLim ((Scheme.Modules.pullback (cC.π.app i)).obj M)
          ((Scheme.Modules.pullback (cC.π.app i)).obj L) n
          ((Scheme.Modules.pullbackTensorPowerIso (cC.π.app i) M n).symm ≪≫
            (Scheme.Modules.pullback (cC.π.app i)).mapIso α)
          (pullbackBoundaryTrivialization (cB.π.app i) (b.app i) bLim
            (cC.π.app i) (hb i) L τ))
    (eAux : (Scheme.Modules.pullback (b.app i)).obj N ≅
      SheafOfModules.unit (B.obj i).ringCatSheaf)
    (hAux : pullbackBoundaryTrivialization (cB.π.app i) (b.app i) bLim (cC.π.app i)
      (hb i) N eAux = ((Scheme.Modules.pullback bLim).mapIso F).symm ≪≫ eN)
    (a₀ : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor cC.pt.sheaf).obj M₀).obj N₀, ⊤))
    (a : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor (C.obj i).sheaf).obj M).obj N, ⊤))
    (ha : Hom.app
      (tensorProductIso cC.pt.sheaf.obj cC.pt.ringCatSheaf.property E F ≪≫
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso (cC.π.app i) M N).symm).hom ⊤ a₀ =
      pullbackGlobalSections (cC.π.app i) _ a)
    (bN : Γ(N, ⊤))
    (hbN : Hom.app eAux.hom ⊤ (pullbackGlobalSections (b.app i) N bN) = (1 : Γ(B.obj i, ⊤)))
    (haOne : Hom.app (Scheme.Modules.pullbackTensorFrame bLim M₀ N₀ eM eN).hom ⊤
      (pullbackGlobalSections bLim _ a₀) = (1 : Γ(cB.pt, ⊤))) :
      ∃ (j : I) (f : j ⟶ i)
        (e : (Scheme.Modules.pullback (b.app j)).obj
          ((Scheme.Modules.pullback (C.map f)).obj M) ≅
            SheafOfModules.unit (B.obj j).ringCatSheaf),
        let m := framePullbackIso (B.map f) (b.app i) (b.app j) (C.map f)
          (b.naturality f) M e
        ((Scheme.Modules.pullback (cB.π.app j)).map m.hom ≫
            canHom (cB.π.app j) (B.map f) (cB.π.app i) (cB.w f) (SheafOfModules.unit (B.obj
              i).ringCatSheaf) =
          canHom (cB.π.app j) (B.map f) (cB.π.app i) (cB.w f) ((Scheme.Modules.pullback (b.app
            i)).obj M) ≫
            (framePullbackIso (cB.π.app i) (b.app i) bLim (cC.π.app i) (hb i) M
              (((Scheme.Modules.pullback bLim).mapIso E).symm ≪≫ eM)).hom) ∧
        (tensorPowerCongr (B.obj j).toRingedSpace.presheaf
          (structureSheafRing (B.obj j).toRingedSpace).property _ _ e n =
            boundaryRootPowerIso (b.app j) ((Scheme.Modules.pullback (C.map f)).obj M)
              ((Scheme.Modules.pullback (C.map f)).obj L) n
              ((Scheme.Modules.pullbackTensorPowerIso (C.map f) M n).symm ≪≫
                (Scheme.Modules.pullback (C.map f)).mapIso α)
              (pullbackBoundaryTrivialization (B.map f) (b.app i) (b.app j) (C.map f)
                (b.naturality f) L τ)) ∧
        Hom.app
          ((Scheme.Modules.pullback (b.app j)).mapIso
              (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso (C.map f) M N) ≪≫
            Scheme.Modules.pullbackTensorFrame (b.app j)
              ((Scheme.Modules.pullback (C.map f)).obj M)
              ((Scheme.Modules.pullback (C.map f)).obj N) e
              (pullbackBoundaryTrivialization (B.map f) (b.app i) (b.app j) (C.map f)
                (b.naturality f) N eAux)).hom ⊤
          (pullbackGlobalSections (b.app j) _
            (pullbackGlobalSections (C.map f) _ a)) = (1 : Γ(B.obj j, ⊤)) ∧
        Hom.app
          (pullbackBoundaryTrivialization (B.map f) (b.app i) (b.app j) (C.map f)
            (b.naturality f) N eAux).hom ⊤
          (pullbackGlobalSections (b.app j) _
            (pullbackGlobalSections (C.map f) N bN)) = (1 : Γ(B.obj j, ⊤)) := by
  let P (_ : PUnit.{1}) := SheafOfModules.unit (B.obj i).ringCatSheaf
  let (_ : PUnit.{1}) : (P PUnit.unit).IsFinitePresentation := isFinitePresentation_unit (B.obj i)
  let s (_ : PUnit.{1}) := Scheme.Modules.auxiliaryBoundaryNumerator (b.app i) M N eAux a
  let t (_ : PUnit.{1}) := unitHomEquivTop
    (SheafOfModules.unit (B.obj i).ringCatSheaf) (1 : Γ(B.obj i, ⊤))
  have hst (x : PUnit.{1}) : (Scheme.Modules.pullback (cB.π.app i)).map (s x) ≫
      (framePullbackIso (cB.π.app i) (b.app i) bLim (cC.π.app i) (hb i) M
        (((Scheme.Modules.pullback bLim).mapIso E).symm ≪≫ eM)).hom =
      (Scheme.Modules.pullback (cB.π.app i)).map (t x) := by
    exact (Scheme.Modules.auxiliaryBoundaryNumerator_original_one_iff
      (cB.π.app i) (b.app i) bLim (cC.π.app i) (hb i) M N M₀ N₀ E F eM eN eAux hAux
      a₀ a ha).mpr haOne
  obtain ⟨j, f, e, he, hpow, hst'⟩ :=
    exists_boundary_root_frame_comp_eq_of_isLimit_finite B C b cB hcB cC bLim hb i M L n
      α τ (((Scheme.Modules.pullback bLim).mapIso E).symm ≪≫ eM) heLim P s t hst
  refine ⟨j, f, e, he, hpow, ?_, ?_⟩
  · exact (Scheme.Modules.auxiliaryBoundaryNumerator_pullback_one_iff
    (B.map f) (b.app i) (b.app j) (C.map f) (b.naturality f) M N eAux e a).mp
        (hst' PUnit.unit)
  · exact Scheme.Modules.pullbackBoundaryTrivialization_section_one
      (B.map f) (b.app i) (b.app j) (C.map f) (b.naturality f) N eAux bN hbN

end Stacks.AlgebraicGeometry.ModuleLimits
