/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.OriginalRootAuxiliaryFramesConsumerNormalized

/-! # Named full consumer-normalized mathematical conclusion

The definition is a proposition, not a proof-valued definition. It retains the
entire original quantified root/auxiliary input tail and every existential
witness, recovery identity and boundary equation. The bridge theorem is proved
by the existing native theorem. Actual diagram specializations need not elaborate
that expanded proposition a second time.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.Modules
open Stacks.SheafOfModules.Invertible Stacks.Divisors
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
namespace Stacks.AlgebraicGeometry.ModuleLimits
local instance normalizedStatementPullbackInvertible
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    [hM : AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property ((Scheme.Modules.pullback f).obj M) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom M hM

/-- The full original consumer-normalized conclusion, with its original input tail. -/
def OriginalRootAuxiliaryFramesConsumerStatement
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
    (i : I) : Prop :=
  ∀ (M : cC.pt.Modules)
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
      (pullbackGlobalSections bLim _ a₀) = (1 : Γ(cB.pt, ⊤))),
    ∃ (k : I) (e : k ⟶ i) (Mk : (C.obj k).Modules)
      (hMk : AlgebraicGeometry.SheafOfModules.IsInvertible (C.obj k).toRingedSpace.presheaf
        (structureSheafRing (C.obj k).toRingedSpace).property Mk),
      let _ := hMk
      ∃ (eM : M ≅ (Scheme.Modules.pullback (cC.π.app k)).obj Mk) (j : I) (f : j ⟶ k)
        (β : tensorPower (C.obj j).toRingedSpace.presheaf
          (structureSheafRing (C.obj j).toRingedSpace).property
            ((Scheme.Modules.pullback (C.map f)).obj Mk) (n : ℤ) ≅
          (Scheme.Modules.pullback (C.map f)).obj
            ((Scheme.Modules.pullback (C.map e)).obj (differenceSheaf (D i) (E i)))),
      let Mj := (Scheme.Modules.pullback (C.map f)).obj Mk
  let _ : AlgebraicGeometry.SheafOfModules.IsInvertible (C.obj j).sheaf.obj
      (C.obj j).ringCatSheaf.property Mj :=
    Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry
      (C.map f).toLRSHom.toShHom Mk hMk
      let Qk := (Scheme.Modules.pullback (C.map e)).obj (differenceSheaf (D i) (E i))
      let Qj := (Scheme.Modules.pullback (C.map f)).obj Qk
      let eMj := eM ≪≫ (canIso (cC.π.app j) (C.map f) (cC.π.app k) (cC.w f) Mk).symm
      let eL := canIso (cC.π.app j) (C.map f) (cC.π.app k) (cC.w f) Qk ≪≫
        canIso (cC.π.app k) (C.map e) (cC.π.app i) (cC.w e) (differenceSheaf (D i) (E i))
      let τk := pullbackBoundaryTrivialization (B.map e) (b.app i) (b.app k) (C.map e)
        (b.naturality e) (differenceSheaf (D i) (E i)) (differenceSheafBoundaryIso (b.app i) (D
          i) (E i) (aD i) (aE i))
      let τj := pullbackBoundaryTrivialization (B.map f) (b.app k) (b.app j) (C.map f)
        (b.naturality f) Qk τk
      let αj := (Scheme.Modules.pullbackTensorPowerIso (cC.π.app j) Mj n).symm ≪≫
        (Scheme.Modules.pullback (cC.π.app j)).mapIso β
      let eLim := (Scheme.Modules.pullback bLim).mapIso eMj.symm ≪≫ e₀
      (tensorPowerCongr cC.pt.toRingedSpace.presheaf
        (structureSheafRing cC.pt.toRingedSpace).property _ _ eMj n ≪≫ αj ≪≫ eL = α) ∧
      (tensorPowerCongr cB.pt.toRingedSpace.presheaf
        (structureSheafRing cB.pt.toRingedSpace).property _ _ eLim n =
        boundaryRootPowerIso bLim ((Scheme.Modules.pullback (cC.π.app j)).obj Mj)
          ((Scheme.Modules.pullback (cC.π.app j)).obj Qj) n αj
          (pullbackBoundaryTrivialization (cB.π.app j) (b.app j) bLim
            (cC.π.app j) (hb j) Qj τj)) ∧
      ∃ (j' : I) (g : j' ⟶ j) (Nj : (C.obj j').Modules)
        (_hNj : AlgebraicGeometry.SheafOfModules.IsInvertible (C.obj j').sheaf.obj
          (C.obj j').ringCatSheaf.property Nj)
        (F : N₀ ≅ (Scheme.Modules.pullback (cC.π.app j')).obj Nj)
        (eAux : (Scheme.Modules.pullback (b.app j')).obj Nj ≅
          SheafOfModules.unit (B.obj j').ringCatSheaf)
        (a : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor (C.obj j').sheaf).obj
          ((Scheme.Modules.pullback (C.map g)).obj Mj)).obj Nj, ⊤)) (bN : Γ(Nj, ⊤)),
      let ER := Scheme.Modules.refinedSectionModelIso (cC.π.app j') (C.map g)
        (cC.π.app j) (cC.w g) Mj eMj
      let Mj' := (Scheme.Modules.pullback (C.map g)).obj Mj
      let _Qj' := (Scheme.Modules.pullback (C.map g)).obj Qj
      let β' := (Scheme.Modules.pullbackTensorPowerIso (C.map g) Mj n).symm ≪≫
        (Scheme.Modules.pullback (C.map g)).mapIso β
      let _τj' := pullbackBoundaryTrivialization (B.map g) (b.app j) (b.app j') (C.map g)
        (b.naturality g) Qj τj
      let eLim' := (Scheme.Modules.pullback bLim).mapIso
        (canIso (cC.π.app j') (C.map g) (cC.π.app j) (cC.w g) Mj) ≪≫ eLim
      Hom.app
        (tensorProductIso cC.pt.sheaf.obj cC.pt.ringCatSheaf.property ER F ≪≫
          (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso (cC.π.app j') Mj' Nj).symm).hom
        ⊤ a₀ = pullbackGlobalSections (cC.π.app j') _ a ∧
      Hom.app F.hom ⊤ b₀ = pullbackGlobalSections (cC.π.app j') Nj bN ∧
      pullbackBoundaryTrivialization (cB.π.app j') (b.app j') bLim (cC.π.app j') (hb j') Nj eAux =
        ((Scheme.Modules.pullback bLim).mapIso F).symm ≪≫ eN₀ ∧
      Hom.app eAux.hom ⊤ (pullbackGlobalSections (b.app j') Nj bN) = (1 : Γ(B.obj j', ⊤)) ∧
      ∃ (ℓ : I) (h : ℓ ⟶ j')
        (eB : (Scheme.Modules.pullback (b.app ℓ)).obj
          ((Scheme.Modules.pullback (C.map h)).obj Mj') ≅
            SheafOfModules.unit (B.obj ℓ).ringCatSheaf),
      let : IsPullbackDefined (C.map e) (D i) := by
        change IsEffectiveCartierDivisor ((D i).comap (C.map e))
        simpa only [hDmap] using (inferInstance : IsEffectiveCartierDivisor (D k))
      let : IsPullbackDefined (C.map e) (E i) := by
        change IsEffectiveCartierDivisor ((E i).comap (C.map e))
        simpa only [hEmap] using (inferInstance : IsEffectiveCartierDivisor (E k))
      let ρ1 := differenceSheafPullbackIso (C.map e) (D i) (E i)
      let δ1 := ρ1
      let : IsPullbackDefined (C.map f) ((D i).comap (C.map e)) := by
        change IsEffectiveCartierDivisor (((D i).comap (C.map e)).comap (C.map f))
        simpa only [hDmap] using (inferInstance : IsEffectiveCartierDivisor (D j))
      let : IsPullbackDefined (C.map f) ((E i).comap (C.map e)) := by
        change IsEffectiveCartierDivisor (((E i).comap (C.map e)).comap (C.map f))
        simpa only [hEmap] using (inferInstance : IsEffectiveCartierDivisor (E j))
      let ρ2 := differenceSheafPullbackIso (C.map f) ((D i).comap (C.map e)) ((E i).comap (C.map e))
      let δ2 := (Scheme.Modules.pullback (C.map f)).mapIso δ1 ≪≫ ρ2
      let : IsPullbackDefined (C.map g) (((D i).comap (C.map e)).comap (C.map f)) := by
        change IsEffectiveCartierDivisor ((((D i).comap (C.map e)).comap (C.map f)).comap (C.map g))
        simpa only [hDmap] using (inferInstance : IsEffectiveCartierDivisor (D j'))
      let : IsPullbackDefined (C.map g) (((E i).comap (C.map e)).comap (C.map f)) := by
        change IsEffectiveCartierDivisor ((((E i).comap (C.map e)).comap (C.map f)).comap (C.map g))
        simpa only [hEmap] using (inferInstance : IsEffectiveCartierDivisor (E j'))
      let ρ3 := differenceSheafPullbackIso (C.map g) (((D i).comap (C.map e)).comap (C.map f))
        (((E i).comap (C.map e)).comap (C.map f))
      let δ3 := (Scheme.Modules.pullback (C.map g)).mapIso δ2 ≪≫ ρ3
      let : IsPullbackDefined (C.map h) ((((D i).comap (C.map e)).comap (C.map f)).comap (C.map
        g)) := by
        change IsEffectiveCartierDivisor (((((D i).comap (C.map e)).comap (C.map f)).comap
          (C.map g)).comap (C.map h))
        simpa only [hDmap] using (inferInstance : IsEffectiveCartierDivisor (D ℓ))
      let : IsPullbackDefined (C.map h) ((((E i).comap (C.map e)).comap (C.map f)).comap (C.map
        g)) := by
        change IsEffectiveCartierDivisor (((((E i).comap (C.map e)).comap (C.map f)).comap
          (C.map g)).comap (C.map h))
        simpa only [hEmap] using (inferInstance : IsEffectiveCartierDivisor (E ℓ))
      let ρ4 := differenceSheafPullbackIso (C.map h) ((((D i).comap (C.map e)).comap (C.map
        f)).comap (C.map g)) ((((E i).comap (C.map e)).comap (C.map f)).comap (C.map g))
      let δ4 := (Scheme.Modules.pullback (C.map h)).mapIso δ3 ≪≫ ρ4
      let δactual := δ4 ≪≫ eqToIso (congrArg₂ differenceSheaf
        (show (((((D i).comap (C.map e)).comap (C.map f)).comap (C.map g)).comap (C.map h)) = D
          ℓ by simp only [hDmap])
        (show (((((E i).comap (C.map e)).comap (C.map f)).comap (C.map g)).comap (C.map h)) = E
          ℓ by simp only [hEmap]))
      let MFinal := (Scheme.Modules.pullback (C.map h)).obj Mj'
      let NFinal := (Scheme.Modules.pullback (C.map h)).obj Nj
      let eNFinal := pullbackBoundaryTrivialization (B.map h) (b.app j') (b.app ℓ)
        (C.map h) (b.naturality h) Nj eAux
      let aFinal := Hom.app (pullbackTensorIso (C.map h) Mj' Nj).hom ⊤
        (pullbackGlobalSections (C.map h) _ a)
      let bFinal := pullbackGlobalSections (C.map h) Nj bN
      let m := framePullbackIso (B.map h) (b.app j') (b.app ℓ) (C.map h)
        (b.naturality h) Mj' eB
      ((Scheme.Modules.pullback (cB.π.app ℓ)).map m.hom ≫
          canHom (cB.π.app ℓ) (B.map h) (cB.π.app j') (cB.w h)
            (SheafOfModules.unit (B.obj j').ringCatSheaf) =
        canHom (cB.π.app ℓ) (B.map h) (cB.π.app j') (cB.w h)
          ((Scheme.Modules.pullback (b.app j')).obj Mj') ≫
            (framePullbackIso (cB.π.app j') (b.app j') bLim (cC.π.app j') (hb j') Mj' eLim').hom) ∧
      (tensorPowerCongr (B.obj ℓ).toRingedSpace.presheaf
        (structureSheafRing (B.obj ℓ).toRingedSpace).property _ _ eB n =
        boundaryRootPowerIso (b.app ℓ) ((Scheme.Modules.pullback (C.map h)).obj Mj')
          (differenceSheaf (D ℓ) (E ℓ)) n
          (((Scheme.Modules.pullbackTensorPowerIso (C.map h) Mj' n).symm ≪≫
            (Scheme.Modules.pullback (C.map h)).mapIso β') ≪≫ δactual)
          (differenceSheafBoundaryIso (b.app ℓ) (D ℓ) (E ℓ) (aD ℓ) (aE ℓ))) ∧
      Hom.app (Scheme.Modules.pullbackTensorFrame (b.app ℓ)
        MFinal NFinal eB eNFinal).hom ⊤
        (pullbackGlobalSections (b.app ℓ) _ aFinal) = (1 : Γ(B.obj ℓ, ⊤)) ∧
      Hom.app eNFinal.hom ⊤ (pullbackGlobalSections (b.app ℓ) NFinal bFinal) =
        (1 : Γ(B.obj ℓ, ⊤))

/-- Native descent proves the named statement without dropping any recovery data. -/
theorem originalRootAuxiliaryFramesConsumerStatement_of_isLimit
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
    : OriginalRootAuxiliaryFramesConsumerStatement
      B C b cB cC bLim hb D E hDmap hEmap aD aE i := by
  exact exists_original_root_auxiliaryFrames_consumer_normalized_of_isLimit
    B C b cB hcB cC hcC bLim hb D E hDmap hEmap aD aE i

end Stacks.AlgebraicGeometry.ModuleLimits
