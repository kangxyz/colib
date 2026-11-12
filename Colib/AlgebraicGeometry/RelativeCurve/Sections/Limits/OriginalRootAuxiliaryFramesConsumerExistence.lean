/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.OriginalRootAuxiliaryFramesConsumerResult
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

local instance existenceResultRingedInvertible (X : Scheme.{u}) (M : X.Modules)
    [hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hM

local instance existenceResultPullbackInvertible {X Y : Scheme.{u}}
    (b : X ⟶ Y) (M : Y.Modules)
    [Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (ringSheafCond X)
      ((Scheme.Modules.pullback b).obj M) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.PullbackMonoidalSheaf.isInvertible_pullbackFunctor_obj b.toLRSHom.toShHom M)

local instance existenceResultUnitInvertible (X : Scheme.{u}) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (ringSheafCond X)
      (SheafOfModules.unit X.ringCatSheaf) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.SheafOfModules.isInvertible_unit _ _)



/-- Complete original witnesses together with the full descent Result for them. -/
def OriginalRootAuxiliaryFramesConsumerExistence
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
    (n : ℕ) : Prop :=
  let τStage := differenceSheafBoundaryIso (b.app i) (D i) (E i) (aD i) (aE i)
  let τLim := pullbackBoundaryTrivialization (cB.π.app i) (b.app i) bLim
    (cC.π.app i) (hb i) (differenceSheaf (D i) (E i)) τStage
  ∃ (M : cC.pt.Modules)
    (hM : Stacks.SheafOfModules.IsInvertible cC.pt.presheaf cC.pt.ringCatIsSheaf M),
    let _ := hM
    let _ : AlgebraicGeometry.SheafOfModules.IsInvertible cC.pt.toRingedSpace.presheaf
      (structureSheafRing cC.pt.toRingedSpace).property M := hM.toAlgebraicGeometry
    ∃ (α : tensorPower cC.pt.toRingedSpace.presheaf
        (structureSheafRing cC.pt.toRingedSpace).property M (n : ℤ) ≅
        (Scheme.Modules.pullback (cC.π.app i)).obj (differenceSheaf (D i) (E i)))
      (e : (Scheme.Modules.pullback bLim).obj M ≅ SheafOfModules.unit cB.pt.ringCatSheaf)
      (he : tensorPowerCongr cB.pt.presheaf (ringSheafCond cB.pt) _ _ e n =
        boundaryRootPowerIso bLim M _ n α τLim)
      (Naux : cC.pt.Modules)
      (hNaux : AlgebraicGeometry.SheafOfModules.IsInvertible cC.pt.sheaf.obj
        cC.pt.ringCatSheaf.property Naux)
      (a : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor cC.pt.sheaf).obj M).obj Naux, ⊤))
      (bN : Γ(Naux, ⊤))
      (eN : (Scheme.Modules.pullback bLim).obj Naux ≅ SheafOfModules.unit cB.pt.ringCatSheaf)
      (hbN : Scheme.Modules.Hom.app (X := cB.pt) eN.hom ⊤ (pullbackGlobalSections bLim Naux bN) =
        (1 : Γ(cB.pt, ⊤)))
      (haB : Scheme.Modules.Hom.app (X := cB.pt)
        (Scheme.Modules.pullbackTensorFrame bLim M Naux e eN).hom ⊤
        (pullbackGlobalSections bLim _ a) = (1 : Γ(cB.pt, ⊤))),
      a ≠ 0 ∧ bN ≠ 0 ∧
      OriginalRootAuxiliaryFramesConsumerResult
        B C b cB cC bLim hb D E hDmap hEmap aD aE i
        M n α e he Naux hNaux a bN eN hbN haB

/-- Consume the genuine root output once and descend precisely its selected data. -/
theorem originalRootAuxiliaryFramesConsumerExistence_of_output
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (B C : I ⥤ Scheme.{u})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (B.map f)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (C.map f)]
    (b : B ⟶ C) (cB : Cone B) (hcB : IsLimit cB)
    [∀ i, CompactSpace (B.obj i)] [∀ i, QuasiSeparatedSpace (B.obj i)]
    (cC : Cone C) (hcC : IsLimit cC)
    [∀ i, CompactSpace (C.obj i)] [∀ i, QuasiSeparatedSpace (C.obj i)]
    (bLim : cB.pt ⟶ cC.pt)
    (hb : ∀ i, cB.π.app i ≫ b.app i = bLim ≫ cC.π.app i)
    (D E : ∀ a : I, (C.obj a).IdealSheafData)
    [∀ a, Stacks.Divisors.IsEffectiveCartierDivisor (D a)]
    [∀ a, Stacks.Divisors.IsEffectiveCartierDivisor (E a)]
    (hDmap : ∀ {a d : I} (v : a ⟶ d), (D d).comap (C.map v) = D a)
    (hEmap : ∀ {a d : I} (v : a ⟶ d), (E d).comap (C.map v) = E a)
    (aD : ∀ a (y : B.obj a), b.app a y ∉ (D a).support)
    (aE : ∀ a (y : B.obj a), b.app a y ∉ (E a).support)
    (i : I) [(Stacks.Divisors.differenceSheaf (D i) (E i)).IsFinitePresentation]
    (n : ℕ)
    (H : FullBoundaryRootAuxiliaryOutput bLim
      ((Scheme.Modules.pullback (cC.π.app i)).obj (differenceSheaf (D i) (E i)))
      (pullbackBoundaryTrivialization (cB.π.app i) (b.app i) bLim
        (cC.π.app i) (hb i) (differenceSheaf (D i) (E i))
        (differenceSheafBoundaryIso (b.app i) (D i) (E i) (aD i) (aE i))) n) :
    OriginalRootAuxiliaryFramesConsumerExistence
      B C b cB cC bLim hb D E hDmap hEmap aD aE i n := by
  obtain ⟨M, hM, α, e, he, Naux, hNaux, a, bN, eN, ha, hbnonzero, haB, hbN⟩ := H
  let := hM
  let : AlgebraicGeometry.SheafOfModules.IsInvertible cC.pt.toRingedSpace.presheaf
      (structureSheafRing cC.pt.toRingedSpace).property M := hM.toAlgebraicGeometry
  refine ⟨M, hM, α, e, he, Naux, hNaux, a, bN, eN, hbN, haB, ha, hbnonzero, ?_⟩
  exact originalRootAuxiliaryFramesConsumerResult_of_isLimit
    B C b cB hcB cC hcC bLim hb D E hDmap hEmap aD aE i
    M n α e he Naux hNaux a bN eN hbN haB

end Stacks.AlgebraicGeometry.ModuleLimits
