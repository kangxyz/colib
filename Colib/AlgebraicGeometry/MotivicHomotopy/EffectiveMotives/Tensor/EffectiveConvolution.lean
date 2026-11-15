/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.EffectiveCoproducts
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.ParameterA1Descent
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.RepresentableLocalization
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ConvolutionSymmetry
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ProjectiveBifunctorCoproducts
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ProjectiveBifunctorTriangulated
import Colib.AlgebraicGeometry.PresheavesWithTransfers.ProjectiveModel.GeneratorDevissage
import Mathlib.CategoryTheory.Localization.Monoidal.Basic
import Mathlib.CategoryTheory.Localization.Prod
import StacksFrontier.CategoryTheory.Triangulated.Localization.Pretriangulated

/-!
# Convolution on effective motives

Inversion of effective equivalences after tensoring with a represented
parameter extends to all bounded-above complexes by projective dévissage.
The signed swap supplies the other variable. The resulting bifunctor
uses the actual sheafified singular localization in both variables.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.Scheme
open scoped MonoidalCategory ZeroObject CategoryTheory.Prod

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable {k : Type u} [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "PST(" K ")" => LargePresheaves K
local notation "NST(" K ")" => LargeSheaves K
set_option quotPrecheck false in
local notation "D(" K ")" => DerivedCategory.Minus PST(K)
local notation "Base(" K ")" => Spec (CommRingCat.of K)
local notation "DM(" K ")" => EffectiveMotivesMinus K
local notation "q(" K ")" => singularPresheafToEffective K
local notation "j(" K ")" => effectiveMotivesMinusToDerived K
local notation "W(" K ")" => effectivePresheafEquivalences K

/-- The canonical abelian structure on the sheaf target. -/
local instance instAbelianEffectiveConvolution : Abelian NST(k) := SheafWithTransfers.abelian k

variable (F : Cor k ⥤ Cor k ⥤ Cor k) [F.Additive] [∀ X, (F.obj X).Additive]

local instance (T : Cor k) : (F.flip.obj T).Additive where
  map_add := by
    intro X Y f g
    exact congrArg (fun α => α.app T) (F.map_add (f := f) (g := g))

local notation "B(" F ")" => derivedConvolution F
set_option quotPrecheck false in
local notation "Bc(" K "," F ")" => Functor.uncurry.obj (B(F)) ⋙ q(K)

variable (e : ∀ T : SmoothSite Base(k), Cor.graphFunctor k ⋙ F.flip.obj (Cor.mk T) ≅
  SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k)

include e in
private theorem isIso_effectiveConvolution_map_single {P P' : D(k)} (f : P ⟶ P') (hf : W(k) f)
    (T : Cor k) (n : ℤ) :
    IsIso ((q(k)).map (((B(F)).map f).app
      ((singleDerivedMinus k n).obj ((representableLarge k).obj T)))) := by
  let X := (singleDerivedMinus k 0).obj ((representableLarge k).obj T)
  let X' := (singleDerivedMinus k n).obj ((representableLarge k).obj T)
  let b := derivedConvolutionParameterIso F T
  let h := e T.toSmoothSite
  let h₀ := effectiveParameterTensorCompIso h
  let d : (B(F)).flip.obj X ⋙ q(k) ≅ q(k) ⋙ effectiveParameterTensor h :=
    Functor.isoWhiskerRight b q(k) ≪≫ h₀.symm
  obtain ⟨Z, g, r, hT⟩ := distinguished_cocone_triangle f
  let K := Triangle.mk f g r
  have hz : IsZero ((q(k)).obj Z) :=
    (Triangle.isZero₃_iff_isIso₁ _ ((q(k)).map_distinguished K hT)).2 hf
  have hX : IsZero ((q(k)).obj (((B(F)).obj Z).obj X)) :=
    ((effectiveParameterTensor h).map_isZero hz).of_iso (d.app Z)
  obtain ⟨c, _⟩ := projectiveDerivedMinusBifunctor_exact_right (convolutionBifunctor F) Z
  let V := (B(F)).obj Z
  let : V.CommShift ℤ := c
  let s := singleDerivedMinusShiftIso ((representableLarge k).obj T) n
  let e₀ := (q(k)).mapIso (V.mapIso s.symm ≪≫ (V.commShiftIso (-n)).app X) ≪≫
    ((q(k)).commShiftIso (-n)).app (V.obj X)
  have hY : IsZero ((q(k)).obj (V.obj X')) := ((shiftFunctor DM(k) (-n)).map_isZero hX).of_iso e₀
  obtain ⟨c', h'⟩ := projectiveDerivedMinusBifunctor_exact_left (convolutionBifunctor F) X'
  let V' := (B(F)).flip.obj X'
  let : V'.CommShift ℤ := c'
  let : V'.IsTriangulated := h'
  exact (Triangle.isZero₃_iff_isIso₁ _ ((V' ⋙ q(k)).map_distinguished K hT)).1 hY

include e in
private theorem isIso_effectiveConvolution_map_left {P P' : D(k)} (f : P ⟶ P')
    (hf : W(k) f) (K : D(k)) : IsIso ((q(k)).map (((B(F)).map f).app K)) := by
  let V := (B(F)).obj P
  let V' := (B(F)).obj P'
  let E := q(k) ⋙ j(k)
  let r := Functor.whiskerRight ((B(F)).map f) E
  obtain ⟨c, hc⟩ := projectiveDerivedMinusBifunctor_exact_right (convolutionBifunctor F) P
  obtain ⟨c', hc'⟩ := projectiveDerivedMinusBifunctor_exact_right (convolutionBifunctor F) P'
  let : V.CommShift ℤ := c
  let : V'.CommShift ℤ := c'
  let : V.IsTriangulated := hc
  let : V'.IsTriangulated := hc'
  obtain ⟨b, hb⟩ := P.property
  obtain ⟨b', hb'⟩ := P'.property
  let a := max b b'
  let t := DerivedCategory.TStructure.t (C := PST(k))
  let : P.obj.IsLE b := hb
  let : P'.obj.IsLE b' := hb'
  let : P.obj.IsLE a := t.isLE_of_le _ b _ (le_max_left _ _)
  let : P'.obj.IsLE a := t.isLE_of_le _ b' _ (le_max_right _ _)
  have hLE (X Y : D(k)) (x : ℤ) (hX : X.obj.IsLE a) (hY : Y.obj.IsLE x) :
      (E.obj (((B(F)).obj X).obj Y)).IsLE (x + a) := by
    let _ := hX
    let _ := hY
    rw [add_comm x a]
    exact singularPresheafToEffective_isLE k _ _
      (projectiveDerivedMinusBifunctor_isLE (convolutionBifunctor F) X Y a x)
  have hSum (X : D(k)) (hX : X.obj.IsLE a) (I : Type (u + 1)) (A : I → Cor k) (n : ℤ) :
      PreservesColimit (Discrete.functor fun i =>
        (singleDerivedMinus k n).obj ((representableLarge k).obj (A i)))
        ((B(F)).obj X ⋙ E) := by
    let D₀ := Discrete.functor fun i =>
      (singleDerivedMinus k n).obj ((representableLarge k).obj (A i))
    let Y := (B(F)).obj X
    let Y₀ := fun i => Y.obj (D₀.obj (Discrete.mk i))
    let j := DerivedCategory.Minus.ι (C := PST(k))
    let : PreservesColimit D₀ (Y ⋙ j) :=
      derivedConvolution_preservesRepresentableSingleCoproduct_right F X I A n
    let : ReflectsColimitsOfShape (Discrete I) j :=
      (fullyFaithful_reflectsColimits j).reflectsColimitsOfShape
    let : PreservesColimit D₀ Y := preservesColimit_of_reflects_of_preserves Y j
    have hY (i : I) : (Y₀ i).obj.IsLE (a + n) := by
      let _ := hX
      let : (D₀.obj (Discrete.mk i)).obj.IsLE n := inferInstanceAs
        ((DerivedCategory.Q.obj ((CochainComplex.singleFunctor PST(k) n).obj
          ((representableLarge k).obj (A i)))).IsLE n)
      exact projectiveDerivedMinusBifunctor_isLE (convolutionBifunctor F) X
        (D₀.obj (Discrete.mk i)) a n
    let : PreservesColimit (Discrete.functor Y₀) E :=
      singularPresheafToEffectiveToDerived_preservesColimit k Y₀ (a + n) hY
    let d : D₀ ⋙ Y ≅ Discrete.functor Y₀ := Discrete.natIso (fun _ => Iso.refl _)
    let : PreservesColimit (D₀ ⋙ Y) E := preservesColimit_of_iso_diagram E d.symm
    exact comp_preservesColimit Y E
  have hR (T : Cor k) (n : ℤ) :
      IsIso (r.app ((singleDerivedMinus k n).obj ((representableLarge k).obj T))) := by
    let X := (singleDerivedMinus k n).obj ((representableLarge k).obj T)
    let u := (q(k)).map (((B(F)).map f).app X)
    let : IsIso u := isIso_effectiveConvolution_map_single F e f hf T n
    change IsIso ((j(k)).map u)
    infer_instance
  let : IsIso (r.app K) := isIso_app_of_isIso_singleDerivedMinus_representable k r hR
    (hSum P inferInstance) (hSum P' inferInstance) a
    (fun Y x hY => hLE P Y x inferInstance hY)
    (fun Y x hY => hLE P' Y x inferInstance hY) K
  let u := (q(k)).map (((B(F)).map f).app K)
  have h : IsIso ((j(k)).map u) := by
    change IsIso (r.app K)
    infer_instance
  exact isIso_of_reflects_iso u (j(k))

variable (s : F ≅ F.flip)
  (hs : ∀ X Y, (s.hom.app X).app Y ≫ (s.hom.app Y).app X = 𝟙 _)

include e s hs in
/-- The signed convolution followed by effective localization inverts
effective equivalences in either input. -/
theorem effectiveConvolution_inverts : ((W(k)).prod (W(k))).IsInvertedBy (Bc(k,F)) := by
  intro P Q f hf
  let τ := derivedConvolutionSwap F s hs
  have h₁ : IsIso ((q(k)).map (((B(F)).map f.1).app P.2)) :=
    isIso_effectiveConvolution_map_left F e f.1 hf.1 P.2
  have h₂ : IsIso ((q(k)).map (((B(F)).obj Q.1).map f.2)) := by
    let v := Functor.isoWhiskerRight (τ.app Q.1) q(k)
    exact (NatIso.isIso_map_iff v f.2).2 (isIso_effectiveConvolution_map_left F e f.2 hf.2 Q.1)
  have h : ((Bc(k,F)).map f) =
      (q(k)).map (((B(F)).map f.1).app P.2) ≫ (q(k)).map (((B(F)).obj Q.1).map f.2) :=
    (q(k)).map_comp _ _
  rw [h]
  infer_instance

include e s hs in
/-- Effective equivalences are monoidal for a coherent structure whose
actual tensor is the signed projective convolution. -/
theorem effectivePresheafEquivalences_isMonoidal [MonoidalCategory D(k)]
    (d : MonoidalCategory.curriedTensor D(k) ≅ derivedConvolution F) : (W(k)).IsMonoidal := by
  apply MorphismProperty.IsMonoidal.mk'
  intro X X' Y Y' f g hf hg
  let b := Functor.isoWhiskerRight (Functor.uncurry.mapIso d) (q(k))
  have h : IsIso ((Bc(k,F)).map (f ×ₘ g)) :=
    effectiveConvolution_inverts F e s hs (f ×ₘ g) ⟨hf, hg⟩
  change IsIso ((q(k)).map (f ⊗ₘ g))
  rw [MonoidalCategory.tensorHom_def]
  exact (NatIso.isIso_map_iff b (f ×ₘ g)).2 h

/-- The actual effective tensor on the product category. -/
def effectiveConvolution : DM(k) × DM(k) ⥤ DM(k) :=
  Localization.lift (Bc(k,F)) (effectiveConvolution_inverts F e s hs) ((q(k)).prod (q(k)))

/-- Applying the actual effective tensor to localized presheaf complexes
agrees with localizing their signed total convolution. -/
def effectiveConvolutionCompIso : (q(k)).prod (q(k)) ⋙ effectiveConvolution F e s hs ≅ Bc(k,F) :=
  Localization.fac (Bc(k,F)) (effectiveConvolution_inverts F e s hs) ((q(k)).prod (q(k)))

/-- Localization intertwines signed convolution with a fixed second argument. -/
def effectiveConvolutionLeftCompIso (P : D(k)) :
    q(k) ⋙ CategoryTheory.Prod.sectL DM(k) ((q(k)).obj P) ⋙ effectiveConvolution F e s hs ≅
      (B(F)).flip.obj P ⋙ q(k) := by
  let E := effectiveConvolution F e s hs
  let j := CategoryTheory.Prod.sectL D(k) P
  let j' := CategoryTheory.Prod.sectL DM(k) ((q(k)).obj P)
  let h : q(k) ⋙ j' ≅ j ⋙ (q(k)).prod (q(k)) := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    change ((q(k)).map f ×ₘ 𝟙 ((q(k)).obj P)) ≫ 𝟙 _ =
      𝟙 _ ≫ ((q(k)).map f ×ₘ (q(k)).map (𝟙 P))
    have hm := (q(k)).map_id P
    exact (Category.comp_id _).trans
      (((congrArg (fun g => (q(k)).map f ×ₘ g) hm).symm).trans (Category.id_comp _).symm))
  let h' : j ⋙ Functor.uncurry.obj (B(F)) ≅ (B(F)).flip.obj P :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro X Y f
      change (((B(F)).map f).app P ≫ ((B(F)).obj Y).map (𝟙 P)) ≫ 𝟙 _ =
        𝟙 _ ≫ ((B(F)).map f).app P
      have hM := ((B(F)).obj Y).map_id P
      exact (Category.comp_id _).trans ((congrArg (((B(F)).map f).app P ≫ ·) hM).trans
        ((Category.comp_id _).trans (Category.id_comp _).symm)))
  exact (Functor.associator q(k) j' E).symm ≪≫ Functor.isoWhiskerRight h E ≪≫
    Functor.associator j ((q(k)).prod (q(k))) E ≪≫ Functor.isoWhiskerLeft j
      (effectiveConvolutionCompIso F e s hs) ≪≫
    (Functor.associator j (Functor.uncurry.obj (B(F))) q(k)).symm ≪≫ Functor.isoWhiskerRight h' q(k)

/-- The product of the original represented effective motives is the
motive of the corresponding product of smooth schemes. -/
def effectiveConvolutionRepresentableIso (X Y : Cor k) :
    (effectiveConvolution F e s hs).obj ((effectiveMotive k).obj X, (effectiveMotive k).obj Y) ≅
      (effectiveMotive k).obj ((F.obj X).obj Y) :=
  (effectiveConvolution F e s hs).mapIso ((localizedRepresentableIso X).symm.prod
    (localizedRepresentableIso Y).symm) ≪≫
    (effectiveConvolutionCompIso F e s hs).app
      (((singleDerivedMinus k 0).obj ((representableLarge k).obj X)),
        ((singleDerivedMinus k 0).obj ((representableLarge k).obj Y))) ≪≫
    (q(k)).mapIso (derivedConvolutionRepresentableIso F X Y) ≪≫
    localizedRepresentableIso ((F.obj X).obj Y)

end AlgebraicGeometry.MotivicHomotopy
