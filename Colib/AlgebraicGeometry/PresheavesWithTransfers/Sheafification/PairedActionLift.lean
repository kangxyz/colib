/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Sheafification.MiddleLiftDifference
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.SectionCorrespondences

/-!
# Lifting the original representatives from the four paired actions

The two lambda correspondences and the correction act on the actual original
representatives. Their source and target comparisons are literal graphs of the
restriction maps through the same two section choices.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option quotPrecheck false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Ample Stacks.Divisors Stacks.Morphisms
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.RelativeCurvePencil
open _root_.AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
open _root_.AlgebraicGeometry.Scheme.SmoothSite.Contraction

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k] {S X Y P C A Z D₁ D₂ V : Scheme.{u}}
  [IsAffine S] [IsAffine X] [IsAffine Y] [IsAffine A] [IsAffine V]
  (t : S ⟶ Spec (.of k)) [Smooth t]
  (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (π : P ⟶ S) [IsProper π] (f : C ⟶ P) [IsFinite f]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ f ≫ π)]
  (jA : X ⟶ P) [IsOpenImmersion jA] [SmoothOfRelativeDimension 1 (jA ≫ π)]
  (p : Y ⟶ X) (hRet : j ≫ f = p ≫ jA)
  (hB : j ≫ (f ≫ π) = p ≫ q) (hA : jA ≫ π = (𝟙 X) ≫ q)
  (a : A ⟶ X) [IsOpenImmersion a] [SmoothOfRelativeDimension 1 ((a ≫ jA) ≫ π)]
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 Z) p z)
  (e : divisorSheaf (relativeBoundaryGraph q z).ker ≅
    SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf)
  (d₁ : D₁ ⟶ C) (hd₁ : Disjoint (Set.range j) (Set.range d₁))
  (d₂ : D₂ ⟶ P)
  (hd₂ : Disjoint (Set.range jA) (Set.range d₂))
  (ha : Disjoint (Set.range a) (Set.range z))
  (c₁ : SectionData q (f ≫ π) j p hB a z s hs H e d₁ hd₁ ha)
  (c₂ : SectionData q π jA (𝟙 X) hA a z z (Category.comp_id z) (IsPullback.of_id_snd)
    e d₂ hd₂ ha)
  (v : V ⟶ C) [IsOpenImmersion v] [SmoothOfRelativeDimension 1 (v ≫ f ≫ π)]
  (u : V ⟶ Y) (hu : u ≫ j = v) (g : V ⟶ A) (hg : v ≫ f = g ≫ (a ≫ jA))
  (hc₁ : ∀ x : C, x ∈ Set.range v ∨ x ∈ Set.range d₁ ∨ x ∈ Set.range (s ≫ j))
  (hc₂ : ∀ x : P, x ∈ Set.range (a ≫ jA) ∨ x ∈ Set.range d₂ ∨
    x ∈ Set.range (z ≫ jA))

local notation "b" => (j ≫ f ≫ π)
local notation "bA" => (jA ≫ π)
local notation "rB" => (v ≫ f ≫ π)
local notation "rA" => ((a ≫ jA) ≫ π)

local instance : Smooth q := SmoothOfRelativeDimension.smooth 1 q
local instance : Smooth b := SmoothOfRelativeDimension.smooth 1 b
local instance : Smooth bA := SmoothOfRelativeDimension.smooth 1 bA
local instance : Smooth rB := SmoothOfRelativeDimension.smooth 1 rB
local instance : Smooth rA := SmoothOfRelativeDimension.smooth 1 rA

local notation "Y₀" => (SmoothSite.mk (b ≫ t))
local notation "X₀" => (SmoothSite.mk (bA ≫ t))
local notation "V₀" => (SmoothSite.mk (rB ≫ t))
local notation "A₀" => (SmoothSite.mk ((a ≫ q) ≫ t))
local notation "A₁" => (SmoothSite.mk (rA ≫ t))

local notation "hSourceBase" => (show p ≫ bA = b from by
  rw [← Category.assoc p jA π, ← hRet, Category.assoc])
local notation "hTargetBase" => (show g ≫ rA = rB from by
  rw [← Category.assoc g (a ≫ jA) π, ← hg, Category.assoc])
local notation "ha₀" => (show a ≫ bA = a ≫ q from by rw [hA, Category.id_comp])
local notation "u₀" => (SmoothSite.homMk (X := V₀) (Y := Y₀) u
  ((Category.assoc u b t).symm.trans
    (congrArg (fun w ↦ w ≫ t) ((Category.assoc u j (f ≫ π)).symm.trans
      (congrArg (fun w ↦ w ≫ f ≫ π) hu)))))
local notation "p₀" => (SmoothSite.homMk (X := Y₀) (Y := X₀) p
  ((Category.assoc p bA t).symm.trans (congrArg (fun w ↦ w ≫ t) hSourceBase)))
local notation "g₀" => (SmoothSite.homMk (X := V₀) (Y := A₁) g
  ((Category.assoc g rA t).symm.trans (congrArg (fun w ↦ w ≫ t) hTargetBase)))
local notation "a₀" => (SmoothSite.homMk (X := A₀) (Y := X₀) a
  ((Category.assoc a bA t).symm.trans (congrArg (fun w ↦ w ≫ t) ha₀)))
local notation "I₀" => (show A₀ ≅ A₁ from MorphismProperty.Over.isoMk (Iso.refl A) (by
  change 𝟙 A ≫ (rA ≫ t) = (a ≫ q) ≫ t
  rw [Category.id_comp, Category.assoc a jA π, ha₀]))
local notation "lambdaB₀" => (show Cor.mk Y₀ ⟶ Cor.mk V₀ from c₁.lambda t v hc₁)
local notation "lambdaA₀" => (show Cor.mk X₀ ⟶ Cor.mk A₁ from c₂.lambda t (a ≫ jA) hc₂)
local notation "psi₀" => (show Cor.mk A₀ ⟶ Cor.mk V₀ from c₁.psi t v hc₁)

set_option maxHeartbeats 800000 in
-- The four actions have dependent source and target maps over the same field.
include hRet hu hg hc₁ hc₂ in
/-- The actual four actions obtained from the same chosen pairs lift the two
original matching sections to the whole restricted cylinder. -/
theorem nisnevichImage_wholeCylinder_lift_of_pairedActions
    (Pst : PresheafWithTransfers.{u + 1} k)
    {Xo U U' T Ao Yo Bo : SmoothSite (Spec (.of k))}
    (jU : U ⟶ Xo) (l : U' ⟶ U) [IsOpenImmersion jU.left] [IsOpenImmersion l.left]
    (hne : Nonempty U'.left) (eT : T ≅ affineLineCylinder.obj U)
    (h : affineLineCylinder.obj U' ⟶ T) (he : h ≫ eT.hom = affineLineCylinder.map l)
    (E : X₀ ≅ affineLineCylinder.obj U')
    (i : Ao ⟶ T) (pT : Yo ⟶ T) (oA : Bo ⟶ Ao) (oY : Bo ⟶ Yo)
    (rAo : A₀ ⟶ Ao) (rYo : Y₀ ⟶ Yo) (rBo : V₀ ⟶ Bo)
    (hAo : rAo ≫ i = (a₀ ≫ E.hom) ≫ h) (hYo : rYo ≫ pT = (p₀ ≫ E.hom) ≫ h)
    (hBoA : rBo ≫ oA = g₀ ≫ (I₀).inv ≫ rAo) (hBoY : rBo ≫ oY = u₀ ≫ rYo)
    (hCover : Sieve.ofTwoArrows (a₀ ≫ E.hom) (p₀ ≫ E.hom) ∈
      SmoothSite.nisnevichTopology (Spec (.of k)) (affineLineCylinder.obj U'))
    (σ : ((nisnevichSheafify k).obj Pst).obj.sections (Cor.mk (affineLineCylinder.obj Xo)))
    (sA : (nisnevichImage Pst).sections (Cor.mk Ao))
    (sY : (nisnevichImage Pst).sections (Cor.mk Yo))
    (hm : (nisnevichImage Pst).transfer ((Cor.graphFunctor k).map oA) sA =
      (nisnevichImage Pst).transfer ((Cor.graphFunctor k).map oY) sY)
    (hsA : (nisnevichImageι Pst).hom.app (op (Cor.mk Ao)) sA =
      ((nisnevichSheafify k).obj Pst).obj.transfer
        ((Cor.graphFunctor k).map (i ≫ eT.hom ≫ affineLineCylinder.map jU)) σ)
    (hsY : (nisnevichImageι Pst).hom.app (op (Cor.mk Yo)) sY =
      ((nisnevichSheafify k).obj Pst).obj.transfer
        ((Cor.graphFunctor k).map (pT ≫ eT.hom ≫ affineLineCylinder.map jU)) σ) :
    ((nisnevichImage Pst).transfer (lambdaB₀ ≫ (Cor.graphFunctor k).map u₀) =
      (nisnevichImage Pst).transfer ((Cor.graphFunctor k).map (𝟙 Y₀))) →
    (nisnevichImage Pst).transfer (psi₀ ≫ (Cor.graphFunctor k).map u₀) = 0 →
    (nisnevichImage Pst).transfer (Sub.sub (α := Cor.mk Y₀ ⟶ Cor.mk A₁)
      (lambdaB₀ ≫ (Cor.graphFunctor k).map g₀)
      ((Cor.graphFunctor k).map p₀ ≫ lambdaA₀)) = 0 →
    ((nisnevichImage Pst).transfer (Sub.sub (α := Cor.mk A₀ ⟶ Cor.mk A₁)
        ((Cor.graphFunctor k).map a₀ ≫ lambdaA₀) (psi₀ ≫ (Cor.graphFunctor k).map g₀)) =
      (nisnevichImage Pst).transfer ((Cor.graphFunctor k).map (I₀).hom)) →
    IsOpenImmersion (l ≫ jU).left ∧ Nonempty U'.left ∧
      ∃ z : (nisnevichImage Pst).sections (Cor.mk (affineLineCylinder.obj U')),
        (nisnevichImageι Pst).hom.app (op (Cor.mk (affineLineCylinder.obj U'))) z =
          ((nisnevichSheafify k).obj Pst).obj.transfer
            ((Cor.graphFunctor k).map (affineLineCylinder.map (l ≫ jU))) σ := by
  intro hE₂ hE₄ hE₃ hE₅
  let Q := nisnevichImage Pst
  let γ := Cor.graphFunctor k
  let rA₁ : A₁ ⟶ Ao := (I₀).inv ≫ rAo
  let lambdaA : Cor.mk (affineLineCylinder.obj U') ⟶ Cor.mk Ao :=
    γ.map E.inv ≫ lambdaA₀ ≫ γ.map rA₁
  let lambdaB : Cor.mk Y₀ ⟶ Cor.mk Bo := lambdaB₀ ≫ γ.map rBo
  let ψ : Cor.mk A₀ ⟶ Cor.mk Bo := psi₀ ≫ γ.map rBo
  have hMap {K : SmoothSite (Spec (.of k))} (w : K ⟶ X₀) :
      γ.map (w ≫ E.hom) ≫ γ.map E.inv = γ.map w := by
    have h : (w ≫ E.hom) ≫ E.inv = w :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun f ↦ w ≫ f) E.hom_inv_id).trans (Category.comp_id _))
    exact (γ.map_comp (w ≫ E.hom) E.inv).symm.trans
      (congrArg (fun f : K ⟶ X₀ ↦ γ.map f) h)
  have hLambdaA {K : SmoothSite (Spec (.of k))} (w : K ⟶ X₀) :
      γ.map (w ≫ E.hom) ≫ lambdaA =
        (γ.map w ≫ lambdaA₀) ≫ γ.map rA₁ := by
    calc
      _ = (γ.map (w ≫ E.hom) ≫ γ.map E.inv) ≫ (lambdaA₀ ≫ γ.map rA₁) :=
        (Category.assoc _ _ _).symm
      _ = γ.map w ≫ (lambdaA₀ ≫ γ.map rA₁) :=
        congrArg (fun f : Cor.mk K ⟶ Cor.mk X₀ ↦ f ≫ (lambdaA₀ ≫ γ.map rA₁)) (hMap w)
      _ = _ := (Category.assoc _ _ _).symm
  have hPost {D : Cor k} {M R : SmoothSite (Spec (.of k))}
      (δ : D ⟶ Cor.mk V₀) (o : Bo ⟶ R) (u' : V₀ ⟶ M) (r : M ⟶ R)
      (hr : rBo ≫ o = u' ≫ r) :
      (δ ≫ γ.map rBo) ≫ γ.map o = (δ ≫ γ.map u') ≫ γ.map r := by
    have h : γ.map rBo ≫ γ.map o = γ.map u' ≫ γ.map r :=
      (γ.map_comp rBo o).symm.trans
        ((congrArg (fun f : V₀ ⟶ R ↦ γ.map f) hr).trans (γ.map_comp u' r))
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun f : Cor.mk V₀ ⟶ Cor.mk R ↦ δ ≫ f) h).trans (Category.assoc _ _ _).symm)
  have hLambdaBA : lambdaB ≫ γ.map oA = (lambdaB₀ ≫ γ.map g₀) ≫ γ.map rA₁ :=
    hPost lambdaB₀ oA g₀ rA₁ hBoA
  have hψA : ψ ≫ γ.map oA = (psi₀ ≫ γ.map g₀) ≫ γ.map rA₁ :=
    hPost psi₀ oA g₀ rA₁ hBoA
  have hBu : Q.transfer (lambdaB ≫ γ.map oY) = Q.transfer (γ.map rYo) := by
    have hId : Q.transfer (γ.map (𝟙 Y₀)) = 𝟙 (Q.sections (Cor.mk Y₀)) :=
      (congrArg (fun f : Cor.mk Y₀ ⟶ Cor.mk Y₀ ↦ Q.transfer f) (γ.map_id Y₀)).trans
        (transfer_id Q (Cor.mk Y₀))
    calc
      _ = Q.transfer ((lambdaB₀ ≫ γ.map u₀) ≫ γ.map rYo) :=
        congrArg (fun f : Cor.mk Y₀ ⟶ Cor.mk Yo ↦ Q.transfer f) (hPost lambdaB₀ oY u₀ rYo hBoY)
      _ = Q.transfer (γ.map rYo) ≫ Q.transfer (lambdaB₀ ≫ γ.map u₀) :=
        transfer_comp Q _ _
      _ = Q.transfer (γ.map rYo) ≫ Q.transfer (γ.map (𝟙 Y₀)) :=
        congrArg (fun f ↦ Q.transfer (γ.map rYo) ≫ f) hE₂
      _ = _ := (congrArg (fun f ↦ Q.transfer (γ.map rYo) ≫ f) hId).trans (Category.comp_id _)
  have hBg : Q.transfer (Sub.sub (α := Cor.mk Y₀ ⟶ Cor.mk Ao)
      (lambdaB ≫ γ.map oA) (γ.map (p₀ ≫ E.hom) ≫ lambdaA)) = 0 := by
    let d : Cor.mk Y₀ ⟶ Cor.mk A₁ :=
      Sub.sub (α := Cor.mk Y₀ ⟶ Cor.mk A₁) (lambdaB₀ ≫ γ.map g₀) (γ.map p₀ ≫ lambdaA₀)
    have hd : Sub.sub (α := Cor.mk Y₀ ⟶ Cor.mk Ao)
        (lambdaB ≫ γ.map oA) (γ.map (p₀ ≫ E.hom) ≫ lambdaA) = d ≫ γ.map rA₁ :=
      (congrArg₂ Sub.sub hLambdaBA (hLambdaA p₀)).trans (Preadditive.sub_comp _ _ _).symm
    calc
      _ = Q.transfer (d ≫ γ.map rA₁) :=
        congrArg (fun f : Cor.mk Y₀ ⟶ Cor.mk Ao ↦ Q.transfer f) hd
      _ = Q.transfer (γ.map rA₁) ≫ Q.transfer d := transfer_comp Q _ _
      _ = Q.transfer (γ.map rA₁) ≫ 0 :=
        congrArg (fun f ↦ Q.transfer (γ.map rA₁) ≫ f) hE₃
      _ = 0 := comp_zero
  have hψu : Q.transfer (ψ ≫ γ.map oY) = 0 := by
    calc
      _ = Q.transfer ((psi₀ ≫ γ.map u₀) ≫ γ.map rYo) :=
        congrArg (fun f : Cor.mk A₀ ⟶ Cor.mk Yo ↦ Q.transfer f) (hPost psi₀ oY u₀ rYo hBoY)
      _ = Q.transfer (γ.map rYo) ≫ Q.transfer (psi₀ ≫ γ.map u₀) := transfer_comp Q _ _
      _ = Q.transfer (γ.map rYo) ≫ 0 := congrArg (fun f ↦ Q.transfer (γ.map rYo) ≫ f) hE₄
      _ = 0 := comp_zero
  have hA' : Q.transfer (Sub.sub (α := Cor.mk A₀ ⟶ Cor.mk Ao)
      (γ.map (a₀ ≫ E.hom) ≫ lambdaA) (ψ ≫ γ.map oA)) =
      Q.transfer (γ.map rAo) := by
    let d : Cor.mk A₀ ⟶ Cor.mk A₁ :=
      Sub.sub (α := Cor.mk A₀ ⟶ Cor.mk A₁) (γ.map a₀ ≫ lambdaA₀) (psi₀ ≫ γ.map g₀)
    have hd : Sub.sub (α := Cor.mk A₀ ⟶ Cor.mk Ao)
        (γ.map (a₀ ≫ E.hom) ≫ lambdaA) (ψ ≫ γ.map oA) = d ≫ γ.map rA₁ :=
      (congrArg₂ Sub.sub (hLambdaA a₀) hψA).trans (Preadditive.sub_comp _ _ _).symm
    have hr : (I₀).hom ≫ rA₁ = rAo := Iso.hom_inv_id_assoc _ _
    calc
      _ = Q.transfer (d ≫ γ.map rA₁) :=
        congrArg (fun f : Cor.mk A₀ ⟶ Cor.mk Ao ↦ Q.transfer f) hd
      _ = Q.transfer (γ.map rA₁) ≫ Q.transfer d := transfer_comp Q _ _
      _ = Q.transfer (γ.map rA₁) ≫ Q.transfer (γ.map (I₀).hom) :=
        congrArg (fun f ↦ Q.transfer (γ.map rA₁) ≫ f) hE₅
      _ = Q.transfer (γ.map (I₀).hom ≫ γ.map rA₁) := (transfer_comp Q _ _).symm
      _ = Q.transfer (γ.map ((I₀).hom ≫ rA₁)) :=
        congrArg (fun f : Cor.mk A₀ ⟶ Cor.mk Ao ↦ Q.transfer f) (γ.map_comp (I₀).hom rA₁).symm
      _ = _ := congrArg (fun f : A₀ ⟶ Ao ↦ Q.transfer (γ.map f)) hr
  exact nisnevichImage_wholeCylinder_lift_of_middle_difference_relations Pst jU l hne eT h he
    i pT oA oY (a₀ ≫ E.hom) (p₀ ≫ E.hom) rAo rYo hAo hYo hCover lambdaA lambdaB ψ
    hBu hBg hψu hA' σ sA sY hm hsA hsY

end AlgebraicGeometry.PresheafWithTransfers
