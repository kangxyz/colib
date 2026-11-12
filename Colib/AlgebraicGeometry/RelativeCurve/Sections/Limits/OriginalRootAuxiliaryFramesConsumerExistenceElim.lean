/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.OriginalRootAuxiliaryFramesConsumerExistence
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.OriginalRootAuxiliaryFramesConsumerResultWithFinal
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.FullBoundaryRootAuxiliaryOutput

/-! # The original root output and its full same-witness descent result

This proposition retains every supplied root/auxiliary witness, both nonzero
conditions, all three boundary equations and the unchanged complete ConsumerResult.
The generic producer destructs the genuine root output once and descends those
same witnesses. Actual diagram specializations can use the same proposition head.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.Modules
open Stacks.Divisors Stacks.SheafOfModules.Invertible
universe u
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
namespace Stacks.AlgebraicGeometry.ModuleLimits

local instance existenceElimRingedInvertible (X : Scheme.{u}) (M : X.Modules)
    [hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hM

local instance existenceElimPullbackInvertible {X Y : Scheme.{u}}
    (b : X ⟶ Y) (M : Y.Modules)
    [Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (ringSheafCond X)
      ((Scheme.Modules.pullback b).obj M) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.PullbackMonoidalSheaf.isInvertible_pullbackFunctor_obj b.toLRSHom.toShHom M)

local instance existenceElimUnitInvertible (X : Scheme.{u}) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (ringSheafCond X)
      (SheafOfModules.unit X.ringCatSheaf) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.SheafOfModules.isInvertible_unit _ _)



/-- Eliminate the original existential only once, consuming its same Result.
The final index is the one occurring in that Result's unchanged terminal leaf. -/
theorem originalRootAuxiliaryFramesConsumerExistence_exists_finish
    {I : Type u} [Category.{u} I]
    (B C : I ⥤ Scheme.{u}) (b : B ⟶ C) (cB : Cone B) (cC : Cone C)
    (bLim : cB.pt ⟶ cC.pt)
    (hb : ∀ i, cB.π.app i ≫ b.app i = bLim ≫ cC.π.app i)
    (D E : ∀ a : I, (C.obj a).IdealSheafData)
    [∀ a, IsEffectiveCartierDivisor (D a)] [∀ a, IsEffectiveCartierDivisor (E a)]
    (hDmap : ∀ {a d : I} (v : a ⟶ d), (D d).comap (C.map v) = D a)
    (hEmap : ∀ {a d : I} (v : a ⟶ d), (E d).comap (C.map v) = E a)
    (aD : ∀ a (y : B.obj a), b.app a y ∉ (D a).support)
    (aE : ∀ a (y : B.obj a), b.app a y ∉ (E a).support)
    (i : I)
    (n : ℕ)
    (Q : I → Prop)
    (H : OriginalRootAuxiliaryFramesConsumerExistence
      B C b cB cC bLim hb D E hDmap hEmap aD aE i n)
    (hConsume : ∀
    (M : cC.pt.Modules)
    [_hM : AlgebraicGeometry.SheafOfModules.IsInvertible cC.pt.toRingedSpace.presheaf
      (structureSheafRing cC.pt.toRingedSpace).property M]
    (α : tensorPower cC.pt.toRingedSpace.presheaf
      (structureSheafRing cC.pt.toRingedSpace).property M (n : ℤ) ≅
        (Scheme.Modules.pullback (cC.π.app i)).obj (differenceSheaf (D i) (E i)))
    (e₀ : (Scheme.Modules.pullback bLim).obj M ≅ SheafOfModules.unit cB.pt.ringCatSheaf)
    (he₀ : tensorPowerCongr cB.pt.toRingedSpace.presheaf
      (structureSheafRing cB.pt.toRingedSpace).property _ _ e₀ n =
        boundaryRootPowerIso bLim M ((Scheme.Modules.pullback (cC.π.app i)).obj (differenceSheaf
          (D i) (E i))) n α
          (pullbackBoundaryTrivialization (cB.π.app i) (b.app i) bLim
            (cC.π.app i) (hb i) (differenceSheaf (D i) (E i)) (differenceSheafBoundaryIso (b.app
              i) (D i) (E i) (aD i) (aE i))))
    (N₀ : cC.pt.Modules)
    (hN₀ : AlgebraicGeometry.SheafOfModules.IsInvertible cC.pt.sheaf.obj
      cC.pt.ringCatSheaf.property N₀)
    (a₀ : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor cC.pt.sheaf).obj M).obj N₀, ⊤))
    (b₀ : Γ(N₀, ⊤))
    (eN₀ : (Scheme.Modules.pullback bLim).obj N₀ ≅ SheafOfModules.unit cB.pt.ringCatSheaf)
    (hb₀ : Hom.app eN₀.hom ⊤ (pullbackGlobalSections bLim N₀ b₀) = (1 : Γ(cB.pt, ⊤)))
    (ha₀ : Hom.app (Scheme.Modules.pullbackTensorFrame bLim M N₀ e₀ eN₀).hom ⊤
      (pullbackGlobalSections bLim _ a₀) = (1 : Γ(cB.pt, ⊤))),
      OriginalRootAuxiliaryFramesConsumerResult
        B C b cB cC bLim hb D E hDmap hEmap aD aE i
        M n α e₀ he₀ N₀ hN₀ a₀ b₀ eN₀ hb₀ ha₀ →
      OriginalRootAuxiliaryFramesConsumerResultWithFinal
        B C b cB cC bLim hb D E hDmap hEmap aD aE i
        M n α e₀ he₀ N₀ hN₀ a₀ b₀ eN₀ hb₀ ha₀
        (fun ℓ _ _ _ _ _ _ _ _ => Q ℓ)) :
    ∃ ℓ, Q ℓ := by
  obtain ⟨M, hM, α, e, he, Naux, hNaux, a, bN, eN, hbN, haB,
    _ha, _hbnonzero, hResult⟩ := H
  let := hM
  let : AlgebraicGeometry.SheafOfModules.IsInvertible cC.pt.toRingedSpace.presheaf
      (structureSheafRing cC.pt.toRingedSpace).property M := hM.toAlgebraicGeometry
  have hFinal := hConsume M α e he Naux hNaux a bN eN hbN haB hResult
  obtain ⟨_k, _eStage, _Mk, _hMk, _eM, _j, _f, _β, _hrec, _hlim, _j', _g, _Nj, _hNj, _F, _eAux,
    _aStage, _bStage, _harec, _hbrec, _hAux, _hbStage, ℓ, _h, _eB, _heB, _hpow, _haFinal,
    _hbFinal, hQ⟩ := hFinal
  exact ⟨ℓ, hQ⟩

end Stacks.AlgebraicGeometry.ModuleLimits
