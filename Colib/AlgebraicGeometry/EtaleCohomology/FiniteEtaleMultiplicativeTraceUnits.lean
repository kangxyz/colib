/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.EtaleCohomology.FiniteEtaleMultiplicativeTraceSplit

/-! # Native multiplicative trace of global units -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
namespace Stacks.EtaleCohomology
open Stacks.Kummer
variable {S Y : Scheme.{u}} (g : Y ⟶ S) [Etale g] [IsFinite g]

/-- Evaluate the native trace on a global unit pulled back from Y. -/
def finiteEtaleMultiplicativeTraceUnits (U : S.Etale) (t : Γ(Y, ⊤)ˣ) : Γ(U.left, ⊤)ˣ :=
  Additive.toMul ((finiteEtaleMultiplicativeTrace g).hom.app (op U)
    (ULift.up (Additive.ofMul
      (Units.map (pullback.snd U.hom g).appTop.hom.toMonoidHom t)))).down

set_option backward.isDefEq.respectTransparency false in
/-- On a split chart the actual global-unit trace is the product along the actual sheets. -/
theorem finiteEtaleMultiplicativeTraceUnits_split (U : S.Etale)
    (h : Stacks.Etale.IsSplitOver g U.hom) (t : Γ(Y, ⊤)ˣ) :
    letI : Finite h.I := h.finite_I
    letI : Fintype h.I := Fintype.ofFinite _
    finiteEtaleMultiplicativeTraceUnits g U t =
      ∏ i, Units.map (h.sheet i).appTop.hom.toMonoidHom t := by
  let : Finite h.I := h.finite_I
  let : Fintype h.I := Fintype.ofFinite _
  have hh := finiteEtaleMultiplicativeTrace_split_apply g U h
    (Units.map (pullback.snd U.hom g).appTop.hom.toMonoidHom t)
  change (Additive.toMul ((finiteEtaleMultiplicativeTrace g).hom.app (op U) _).down) = _
  rw [hh]
  change (∏ i, Units.map (sheetSection g U h rfl i).left.appTop.hom.toMonoidHom
    (Units.map (pullback.snd U.hom g).appTop.hom.toMonoidHom t)) = _
  apply Finset.prod_congr rfl
  intro i _
  apply Units.ext
  change ((pullback.snd U.hom g).appTop ≫
    (sheetSection g U h rfl i).left.appTop).hom t.val = _
  rw [← Scheme.Hom.comp_appTop, sheetSection_left_snd]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Pulling back the actual trace of a global unit commutes with restriction. -/
theorem finiteEtaleMultiplicativeTraceUnits_naturality {U V : S.Etale}
    (f : U ⟶ V) (t : Γ(Y, ⊤)ˣ) :
    Units.map f.left.appTop.hom.toMonoidHom (finiteEtaleMultiplicativeTraceUnits g V t) =
      finiteEtaleMultiplicativeTraceUnits g U t := by
  have hn := ConcreteCategory.congr_hom
    ((finiteEtaleMultiplicativeTrace g).hom.naturality f.op)
    (ULift.up (Additive.ofMul
      (Units.map (pullback.snd V.hom g).appTop.hom.toMonoidHom t)))
  have hm : Units.map ((smallEtaleBaseChange g).map f).left.appTop.hom.toMonoidHom
      (Units.map (pullback.snd V.hom g).appTop.hom.toMonoidHom t) =
        Units.map (pullback.snd U.hom g).appTop.hom.toMonoidHom t := by
    apply Units.ext
    change ((pullback.snd V.hom g).appTop ≫
      ((smallEtaleBaseChange g).map f).left.appTop).hom t.val = _
    rw [← Scheme.Hom.comp_appTop]
    have hw := ((smallEtaleBaseChange g).map f).w
    change ((smallEtaleBaseChange g).map f).left ≫ pullback.snd V.hom g =
      pullback.snd U.hom g ≫ 𝟙 Y at hw
    rw [Category.comp_id] at hw
    rw [hw]
    rfl
  change (finiteEtaleMultiplicativeTrace g).hom.app (op U)
    (ULift.up (Additive.ofMul
      (Units.map ((smallEtaleBaseChange g).map f).left.appTop.hom.toMonoidHom
        (Units.map (pullback.snd V.hom g).appTop.hom.toMonoidHom t)))) = _ at hn
  rw [hm] at hn
  exact congrArg (fun x => Additive.toMul x.down) hn.symm

end Stacks.EtaleCohomology
