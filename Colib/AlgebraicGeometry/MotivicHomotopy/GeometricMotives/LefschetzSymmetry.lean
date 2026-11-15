/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.GeometricMotives.LefschetzBraiding
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.RepresentedBraiding
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.Native
import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.SignedExactness
import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-! # The self-braiding of the effective Lefschetz object -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry.Scheme
open SmoothSite.Contraction
open scoped MonoidalCategory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable {k : Type u} [Field k] [PerfectField k]

local instance lefschetzSymmetryCorSheafify :
    HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (Cor.nisnevichTopology k)

local instance lefschetzSymmetrySmoothSheafify :
    HasSheafify (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k)))

/-- The canonical abelian structure used for the Lefschetz comparison. -/
local instance lefschetzSymmetryAbelian : Abelian (LargeSheaves k) :=
  SheafWithTransfers.abelian k

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

set_option quotPrecheck false in
local notation "S" => Spec (CommRingCat.of k)
set_option quotPrecheck false in
local notation "G" => SmoothSite.multiplicativeGroupObject S
set_option quotPrecheck false in
local notation "E" => EffectiveMotivesMinus k
set_option quotPrecheck false in
local notation "γ" => CategoryTheory.Functor.map (Cor.graphFunctor k)

variable (e : ∀ T : SmoothSite (Spec (CommRingCat.of k)),
  Cor.graphFunctor k ⋙ (curriedTensor (Cor k)).flip.obj (Cor.mk T) ≅
    SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k)

set_option maxHeartbeats 950000 in
-- Compare the projector on the named Laurent splitting and both signed single complexes.
/-- The signed tensor has trivial self-braiding on the original Lefschetz object. -/
theorem effectiveLefschetz_braiding :
    letI := effectiveSignedConvolutionMonoidalCategory e
    letI := effectiveSignedConvolutionSymmetricCategory e
    (β_ (effectiveLefschetzMotive k) (effectiveLefschetzMotive k)).hom = 𝟙 _ := by
  let := effectiveSignedConvolutionMonoidalCategory e
  let := effectiveSignedConvolutionSymmetricCategory e
  let := effectiveSignedConvolutionMonoidalPreadditive e
  let X := Cor.mk G
  let Y := X ⊗ X
  let q := singularPresheafToEffective k
  let y := representableLarge k
  let H (n : ℤ) (W : Cor k) := q.obj ((singleDerivedMinus k n).obj (y.obj W))
  let ψ (n : ℤ) (W : Cor k) := localizedRepresentableShiftIso (k := k) W n
  let f : X ⟶ X := γ (toBase G ≫ SmoothSite.torusOne S)
  let a : X ⟶ X := 𝟙 X - f
  let sh₁ := shiftFunctor E (1 : ℤ)
  let d : sh₁.obj ((effectiveSmoothMotive k).obj G) ≅ H (-1) X := by
    let x := (effectiveMotive k).obj X
    have h₀ : ((effectiveSmoothMotive k).obj G) = x := rfl
    have h₁ : (1 : ℤ) = -(-1 : ℤ) := by decide
    exact eqToIso (congrArg sh₁.obj h₀) ≪≫
      eqToIso (congrArg (fun n => (shiftFunctor E n).obj x) h₁) ≪≫ ψ (-1) X
  let r : Retract (effectiveLefschetzMotive k) (H (-1) X) :=
    ((torusReducedRetract k).map (shiftFunctor E (1 : ℤ))).trans d.retract
  let i := localizedRepresentedTensorIso e X X (-1)
  let p := q.map ((singleDerivedMinus k (-2)).map (y.map (doubleTorusProjector k)))
  let s := q.map ((singleDerivedMinus k (-2)).map (y.map (β_ X X).hom))
  have hv : r.r ≫ r.i = q.map ((singleDerivedMinus k (-1)).map (y.map a)) := by
    have h := localizedRepresentableShiftIso_naturality (k := k) a (-1)
    have h' : (torusReducedRetract k).r ≫ (torusReducedRetract k).i =
        (effectiveMotive k).map a := by
      let M := effectiveMotive k
      let g := Cor.graphFunctor k
      let b := toBase G
      let u := SmoothSite.torusOne S
      have hm : M.map f = M.map (g.map b) ≫ M.map (g.map u) :=
        (M.congr_map (g.map_comp b u)).trans (M.map_comp (g.map b) (g.map u))
      have hs : M.map a = 𝟙 _ - M.map (g.map b) ≫ M.map (g.map u) := by
        have hi : M.map (𝟙 X) = 𝟙 (M.obj (g.obj G)) := M.map_id X
        exact (M.map_sub (f := 𝟙 X) (g := f)).trans (congrArg₂ Sub.sub hi hm)
      exact (torusReducedProjection_inclusion k).trans hs.symm
    dsimp only [r, Retract.trans, Retract.map, Iso.retract]
    simp only [Category.assoc]
    have h₁ : d.hom = (ψ (-1) X).hom := by
      simp only [d, Iso.trans_hom, eqToIso.hom, eqToHom_refl, Category.id_comp]
    rw [← sh₁.map_comp_assoc, h']
    let t := q.map ((singleDerivedMinus k (-1)).map (y.map a))
    have h₃ : sh₁.map ((effectiveMotive k).map a) ≫ d.hom = d.hom ≫ t :=
      (congrArg (sh₁.map ((effectiveMotive k).map a) ≫ ·) h₁).trans
        (h.trans (congrArg (· ≫ t) h₁.symm))
    exact (congrArg (d.inv ≫ ·) h₃).trans (d.inv_hom_id_assoc t)
  have hs : s ≫ p = -p := by
    have h := effectiveMotive_map_swap_comp_doubleTorusProjector k
    have h' : (effectiveMotive k).map (β_ X X).hom ≫
        (effectiveMotive k).map (doubleTorusProjector k) =
          -(effectiveMotive k).map (doubleTorusProjector k) := h
    have hmap (t : Y ⟶ Y) := localizedRepresentableShiftIso_naturality (k := k) t (-2)
    let sh := shiftFunctor E (-(-2 : ℤ))
    let z := (ψ (-2) Y).hom
    have h₁ : z ≫ s = sh.map ((effectiveMotive k).map (β_ X X).hom) ≫ z :=
      (hmap (β_ X X).hom).symm
    have h₂ : z ≫ p = sh.map ((effectiveMotive k).map (doubleTorusProjector k)) ≫ z :=
      (hmap (doubleTorusProjector k)).symm
    let : Epi z := inferInstanceAs (Epi (ψ (-2) Y).hom)
    have hc : z ≫ s ≫ p = z ≫ (-p) := by
      rw [← Category.assoc, h₁, Category.assoc, h₂, ← sh.map_comp_assoc, h',
        sh.map_neg, Preadditive.neg_comp, Preadditive.comp_neg]
      exact congrArg Neg.neg h₂.symm
    exact (cancel_epi z).mp hc
  refine braiding_eq_id_of_signed_retract r i s p ?_ ?_ hs
  · have h := localizedRepresentedTensorIso_braiding e X X (-1)
    change (β_ (H (-1) X) (H (-1) X)).hom ≫ i.hom = -(i.hom ≫ s)
    simpa [i, s] using h
  · rw [hv]
    have h := localizedRepresentedTensorIso_naturality e a a (-1)
    have ha : a ⊗ₘ a = doubleTorusProjector k :=
      (Cor.tensorHom_eq_exteriorProduct a a).trans
        (exteriorProduct_torusComplement k Cor.exteriorGraphProduct)
    rw [ha] at h
    exact h

end AlgebraicGeometry.MotivicHomotopy
