/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.OriginalRootAuxiliaryFramesConsumerResultWithFinal

/-! # Same-witness continuation with an invertible auxiliary module

The existing `WithFinal` predicate is unchanged. This additional eliminator
passes the auxiliary invertibility already present in the original existential
witness to the terminal consumer, in both invertibility conventions.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.Modules
open Stacks.SheafOfModules.Invertible Stacks.Divisors
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
namespace Stacks.AlgebraicGeometry.ModuleLimits
local instance finishedPairResultPullbackInvertible
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    [hM : AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property ((Scheme.Modules.pullback f).obj M) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom M hM


/-- Keep the complete original result and pass both invertible modules to the
terminal consumer. Auxiliary invertibility is obtained from the same descended
witness `Nj`, not assumed for an unrelated terminal module. -/
theorem originalRootAuxiliaryFramesConsumerResult_withFinal_invertiblePair
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
    (M : cC.pt.Modules)
    [hM : AlgebraicGeometry.SheafOfModules.IsInvertible cC.pt.toRingedSpace.presheaf
      (structureSheafRing cC.pt.toRingedSpace).property M] (n : ℕ)
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
      (pullbackGlobalSections bLim _ a₀) = (1 : Γ(cB.pt, ⊤)))
    (Finish : ∀ (ℓ : I) (MR NR : (C.obj ℓ).Modules)
      [AlgebraicGeometry.SheafOfModules.IsInvertible (C.obj ℓ).toRingedSpace.presheaf
        (structureSheafRing (C.obj ℓ).toRingedSpace).property MR],
      (tensorPower (C.obj ℓ).toRingedSpace.presheaf
        (structureSheafRing (C.obj ℓ).toRingedSpace).property MR (n : ℤ) ≅
          differenceSheaf (D ℓ) (E ℓ)) →
      ((Scheme.Modules.pullback (b.app ℓ)).obj MR ≅ SheafOfModules.unit (B.obj ℓ).ringCatSheaf) →
      ((Scheme.Modules.pullback (b.app ℓ)).obj NR ≅ SheafOfModules.unit (B.obj ℓ).ringCatSheaf) →
      Γ(((Stacks.SheafOfModules.Tensor.sheafTensor
        (C.obj ℓ).sheaf).obj MR).obj NR, ⊤) →
      Γ(NR, ⊤) → Prop)
    (H : OriginalRootAuxiliaryFramesConsumerResult
      B C b cB cC bLim hb D E hDmap hEmap aD aE i M n α e₀ he₀ N₀ hN₀ a₀ b₀ eN₀ hb₀ ha₀)
    (hFinish : ∀ (ℓ : I) (MR NR : (C.obj ℓ).Modules)
      [AlgebraicGeometry.SheafOfModules.IsInvertible (C.obj ℓ).toRingedSpace.presheaf
        (structureSheafRing (C.obj ℓ).toRingedSpace).property MR]
      [AlgebraicGeometry.SheafOfModules.IsInvertible (C.obj ℓ).toRingedSpace.presheaf
        (structureSheafRing (C.obj ℓ).toRingedSpace).property NR]
      [Stacks.SheafOfModules.IsInvertible (C.obj ℓ).presheaf (C.obj ℓ).ringCatIsSheaf MR]
      [Stacks.SheafOfModules.IsInvertible (C.obj ℓ).presheaf (C.obj ℓ).ringCatIsSheaf NR]
      (αR : tensorPower (C.obj ℓ).toRingedSpace.presheaf
        (structureSheafRing (C.obj ℓ).toRingedSpace).property MR (n : ℤ) ≅
          differenceSheaf (D ℓ) (E ℓ))
      (eR : (Scheme.Modules.pullback (b.app ℓ)).obj MR ≅ SheafOfModules.unit (B.obj ℓ).ringCatSheaf)
      (eNR : (Scheme.Modules.pullback (b.app ℓ)).obj NR ≅
        SheafOfModules.unit (B.obj ℓ).ringCatSheaf)
      (aR : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor (C.obj ℓ).sheaf).obj MR).obj NR, ⊤))
      (bR : Γ(NR, ⊤)),
      tensorPowerCongr (B.obj ℓ).toRingedSpace.presheaf
        (structureSheafRing (B.obj ℓ).toRingedSpace).property _ _ eR n =
        boundaryRootPowerIso (b.app ℓ) MR _ n αR
          (differenceSheafBoundaryIso (b.app ℓ) (D ℓ) (E ℓ) (aD ℓ) (aE ℓ)) →
      Hom.app (pullbackTensorFrame (b.app ℓ) MR NR eR eNR).hom ⊤
        (pullbackGlobalSections (b.app ℓ) _ aR) = (1 : Γ(B.obj ℓ, ⊤)) →
      Hom.app eNR.hom ⊤ (pullbackGlobalSections (b.app ℓ) NR bR) = (1 : Γ(B.obj ℓ, ⊤)) →
      Finish ℓ MR NR αR eR eNR aR bR) :
    OriginalRootAuxiliaryFramesConsumerResultWithFinal
      B C b cB cC bLim hb D E hDmap hEmap aD aE i M n α e₀ he₀ N₀ hN₀ a₀ b₀ eN₀ hb₀ ha₀ Finish := by
  obtain ⟨k, e, Mk, hMk, eM, j, f, β, hrec, hlim, j', g, Nj, hNj, F, eAux,
    a, bN, harec, hbrec, hAux, hbN, ℓ, h, eB, he, hpow, haFinal, hbFinal⟩ := H
  let := hMk
  let := hNj
  let Mj := (Scheme.Modules.pullback (C.map f)).obj Mk
  let Mj' := (Scheme.Modules.pullback (C.map g)).obj Mj
  let MR := (Scheme.Modules.pullback (C.map h)).obj Mj'
  let NR := (Scheme.Modules.pullback (C.map h)).obj Nj
  let hNR : AlgebraicGeometry.SheafOfModules.IsInvertible
      (C.obj ℓ).toRingedSpace.presheaf
      (structureSheafRing (C.obj ℓ).toRingedSpace).property NR :=
    Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry
      (C.map h).toLRSHom.toShHom Nj hNj
  let : Stacks.SheafOfModules.IsInvertible
      (C.obj ℓ).presheaf (C.obj ℓ).ringCatIsSheaf MR :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inferInstance
  let : Stacks.SheafOfModules.IsInvertible
      (C.obj ℓ).presheaf (C.obj ℓ).ringCatIsSheaf NR :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hNR
  refine ⟨k, e, Mk, hMk, eM, j, f, β, hrec, hlim, j', g, Nj, hNj, F, eAux,
    a, bN, harec, hbrec, hAux, hbN, ℓ, h, eB, he, hpow, haFinal, hbFinal, ?_⟩
  exact hFinish ℓ _ _ _ _ _ _ _ hpow haFinal hbFinal

end Stacks.AlgebraicGeometry.ModuleLimits
