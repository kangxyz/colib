/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.NisnevichLocalization
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.ParameterDerivedForget
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.ParameterDerivedHom
import StacksFrontier.CategoryTheory.Triangulated.LocalizingQuotient
import Colib.CategoryTheory.Functor.LocalEquivalenceOfHomEquiv

/-!
# Nisnevich descent of tensoring with a represented parameter

Derived tensor by a represented parameter is left adjoint, on the
bounded-above source, to the original derived sheaf parameter sections.
The adjunction inverts the maps inverted by exact sheafification, giving
the bounded-above sheaf tensor by Verdier descent.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable {k : Type u} [Field k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "PST(" K ")" => LargePresheaves K
local notation "NST(" K ")" => LargeSheaves K
local notation "a(" K ")" => derivedNisnevichSheafification K
set_option quotPrecheck false in
local notation "aD(" K ")" => (nisnevichSheafify K).mapDerivedCategory
set_option quotPrecheck false in
local notation "i(" K ")" => DerivedCategory.Minus.ι (C := NST(K))

/-- The canonical abelian structure on the sheaf target. -/
local instance instAbelianParameterNisnevichDescent : Abelian NST(k) := SheafWithTransfers.abelian k

variable {T : SmoothSite (Spec (.of k))} {F : Cor k ⥤ Cor k} [F.Additive]
  (e : Cor.graphFunctor k ⋙ F ≅
    SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k)

local notation "L(" F ")" => derivedParameterPushforward F
local notation "R(" comparison ")" => parameterSectionsDerived comparison

/-- The actual projective parameter tensor followed by sheafification. -/
abbrev projectiveParameterNisnevichTensor :
    DerivedCategory.Minus PST(k) ⥤ DerivedCategory.Minus NST(k) :=
  L(F) ⋙ a(k)

/-- Maps from the sheafified tensor transpose to maps into the actual
derived underlying presheaf of the derived sheaf parameter sections. -/
def projectiveParameterNisnevichHomEquiv
    (P : DerivedCategory.Minus PST(k)) (K : DerivedCategory NST(k)) :
    ((i(k)).obj ((projectiveParameterNisnevichTensor (k := k) (F := F)).obj P) ⟶ K) ≃
      (P.obj ⟶ (forgetDerivedFunctor k).obj ((R(e)).obj K)) :=
  ((nisnevichDerivedAdjunction k).homEquiv ((L(F)).obj P).obj K).trans
    ((derivedParameterPushforwardHomEquiv F P ((forgetDerivedFunctor k).obj K)).trans
      ((parameterSectionsDerivedForgetIso e).symm.app K).homToEquiv)

/-- The represented-parameter transpose respects the original maps of the source. -/
theorem projectiveParameterNisnevichHomEquiv_precompose
    {P P' : DerivedCategory.Minus PST(k)} (K : DerivedCategory NST(k)) (f : P' ⟶ P)
    (g : (i(k)).obj ((projectiveParameterNisnevichTensor (k := k) (F := F)).obj P) ⟶ K) :
    projectiveParameterNisnevichHomEquiv e P' K
        ((i(k)).map ((projectiveParameterNisnevichTensor (k := k) (F := F)).map f) ≫ g) =
      f.hom ≫ projectiveParameterNisnevichHomEquiv e P K g := by
  let H := nisnevichDerivedAdjunction k
  let b := (parameterSectionsDerivedForgetIso e).inv.app K
  change derivedParameterPushforwardHomEquiv F P' ((forgetDerivedFunctor k).obj K)
    (H.homEquiv _ _ ((aD(k)).map ((L(F)).map f).hom ≫ g)) ≫ b =
      f.hom ≫ (derivedParameterPushforwardHomEquiv F P ((forgetDerivedFunctor k).obj K)
        (H.homEquiv _ _ g) ≫ b)
  rw [H.homEquiv_naturality_left, derivedParameterPushforwardHomEquiv_precompose, Category.assoc]

include e in
/-- Tensoring with this represented parameter preserves the maps inverted
by derived Nisnevich sheafification. -/
theorem isIso_projectiveParameterNisnevichTensor_map_of_isIso
    {P P' : DerivedCategory.Minus PST(k)} (f : P ⟶ P') (hf : IsIso ((a(k)).map f)) :
    IsIso ((projectiveParameterNisnevichTensor (k := k) (F := F)).map f) := by
  let _ := hf
  apply (isIso_iff_of_reflects_iso _ (i(k))).1
  let H := nisnevichDerivedAdjunction k
  let C := projectiveParameterNisnevichTensor (k := k) (F := F)
  let L := a(k) ⋙ i(k)
  let Q := C ⋙ i(k)
  have : IsIso (L.map f) := inferInstance
  apply Functor.isIso_map_of_naturalHomEquiv (L := L) (T := Q) (R(e)).obj
    (fun P K => (projectiveParameterNisnevichHomEquiv e P K).trans
      (H.homEquiv P.obj ((R(e)).obj K)).symm) _ f
  intro P P' g K h
  dsimp only [Equiv.trans_apply]
  rw [projectiveParameterNisnevichHomEquiv_precompose,
    H.homEquiv_naturality_left_symm]

include e in
/-- The sheafified projective tensor inverts the bounded Nisnevich equivalences. -/
theorem projectiveParameterNisnevichTensor_inverts :
    (nisnevichDerivedMinusKernel k).trW.IsInvertedBy
      (projectiveParameterNisnevichTensor (k := k) (F := F)) :=
  fun _ _ f hf => isIso_projectiveParameterNisnevichTensor_map_of_isIso e f
    ((isIso_derivedNisnevichSheafification_map_iff k f).2 hf)

/-- The represented parameter tensor on the actual bounded-above
derived category of transfer sheaves. -/
def nisnevichParameterTensor : DerivedCategory.Minus NST(k) ⥤ DerivedCategory.Minus NST(k) :=
  Localization.lift (projectiveParameterNisnevichTensor (k := k) (F := F))
    (projectiveParameterNisnevichTensor_inverts e) (a(k))

/-- The descent agrees with tensoring before Nisnevich localization, on
the original maps and objects. -/
def nisnevichParameterTensorCompIso :
    a(k) ⋙ nisnevichParameterTensor e ≅ projectiveParameterNisnevichTensor (k := k) (F := F) :=
  Localization.fac _ (projectiveParameterNisnevichTensor_inverts e) (a(k))

instance : Localization.Lifting (a(k)) (nisnevichDerivedMinusKernel k).trW
    (projectiveParameterNisnevichTensor (k := k) (F := F)) (nisnevichParameterTensor e) :=
  ⟨nisnevichParameterTensorCompIso e⟩

@[no_expose]
instance : (nisnevichParameterTensor e).CommShift ℤ :=
  Functor.commShiftOfLocalization (a(k)) (nisnevichDerivedMinusKernel k).trW ℤ
    (projectiveParameterNisnevichTensor (k := k) (F := F)) (nisnevichParameterTensor e)

instance : (nisnevichParameterTensor e).IsTriangulated := by
  have := Localization.essSurj_mapArrow (a(k)) (nisnevichDerivedMinusKernel k).trW
  exact Functor.isTriangulated_of_localization (a(k)) (nisnevichDerivedMinusKernel k).trW
    (projectiveParameterNisnevichTensor (k := k) (F := F)) (nisnevichParameterTensor e)

end AlgebraicGeometry.MotivicHomotopy
