/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.SmashCofiber
public import Colib.AlgebraicGeometry.MotivicHomotopy.AffineLineMotivicRepresentative
import Colib.CategoryTheory.Sites.Simplicial.ReducedCofiberExact

/-!
# The Tate boundary on reduced cohomology of pointed presheaves

The original Laurent-open cochain sequence after smashing gives
the Tate suspension boundary. For integral and finite motivic
coefficients the pointed affine-line contraction makes the middle
term acyclic for all shifted Hom groups.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CategoryTheory.PointedSimplicialPresheaf
open AlgebraicGeometry.Scheme AlgebraicGeometry.PresheafWithTransfers

universe u d

namespace AlgebraicGeometry.MotivicHomotopy

variable (R : CommRingCat.{u})

local notation "Sᵣ" => Spec R
local notation "Cᵣ" => SmoothSite Sᵣ
local notation "Jᵣ" => SmoothSite.nisnevichTopology Sᵣ
local notation "A" => liftedPointedAffineLine R
local notation "T" => liftedTateSphere R

variable [HasSheafify (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1}]
  [HasDerivedCategory.{d}
    (Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})]

/-- The connecting map is that of the literal smashed Laurent-open sequence. -/
def tateSmashConnecting
    (X : PointedSimplicialPresheaf.{u + 1} (SmoothSite (Spec R))) :
    let G := (uliftPointed.{u + 1, u} Cᵣ).obj (pointedTorus R)
    let N := reducedDerivedChains.{d, u + 1} Cᵣ Jᵣ
    N.obj (Under.smash X T) ⟶ (N.obj (Under.smash X G))⟦(1 : ℤ)⟧ :=
  DerivedCategory.triangleOfSESδ (exists_tateSmashReducedCochains_shortExact R X).choose_spec

/-- The original Tate boundary is natural for maps of the pointed factor. -/
theorem tateSmashConnecting_naturality
    {X Y : PointedSimplicialPresheaf.{u + 1} (SmoothSite (Spec R))} (f : X ⟶ Y) :
    let U := uliftPointed.{u + 1, u} Cᵣ
    let F := reducedDerivedChains.{d, u + 1} Cᵣ Jᵣ
    F.map (Under.smashMap f (𝟙 T)) ≫ tateSmashConnecting R Y =
      tateSmashConnecting R X ≫
        (F.map (Under.smashMap f (𝟙 (U.obj (pointedTorus R)))))⟦(1 : ℤ)⟧' := by
  intro U F
  let G := U.obj (pointedTorus R)
  let N := reducedCochains.{u + 1} Cᵣ Jᵣ
  let a := U.map (pointedLaurentOpen R)
  let b := U.map (toTateSphere R)
  let hX := (exists_tateSmashReducedCochains_shortExact R X).choose_spec
  let hY := (exists_tateSmashReducedCochains_shortExact R Y).choose_spec
  have ha : Under.smashMap f (𝟙 G) ≫ Under.smashMap (𝟙 Y) a =
      Under.smashMap (𝟙 X) a ≫ Under.smashMap f (𝟙 A) := by
    simp only [Under.smashMap_comp, Category.id_comp, Category.comp_id]
    exact congrArg (Under.smashMap f) (Category.comp_id a).symm
  have hb : Under.smashMap f (𝟙 A) ≫ Under.smashMap (𝟙 Y) b =
      Under.smashMap (𝟙 X) b ≫ Under.smashMap f (𝟙 T) := by
    simp only [Under.smashMap_comp, Category.id_comp, Category.comp_id]
    exact congrArg (Under.smashMap f) (Category.comp_id b).symm
  let S := ShortComplex.mk (N.map (Under.smashMap (𝟙 X) a)) (N.map (Under.smashMap (𝟙 X) b))
    (exists_tateSmashReducedCochains_shortExact R X).choose
  let T₀ := ShortComplex.mk
    (N.map (Under.smashMap (𝟙 Y) a)) (N.map (Under.smashMap (𝟙 Y) b))
    (exists_tateSmashReducedCochains_shortExact R Y).choose
  let m : S ⟶ T₀ := ShortComplex.homMk (N.map (Under.smashMap f (𝟙 G)))
    (N.map (Under.smashMap f (𝟙 A))) (N.map (Under.smashMap f (𝟙 T)))
    ((N.map_comp _ _).symm.trans ((N.congr_map ha).trans (N.map_comp _ _)))
    ((N.map_comp _ _).symm.trans ((N.congr_map hb).trans (N.map_comp _ _)))
  exact (DerivedCategory.triangleOfSESδ_naturality hX hY m).symm

/-- The original Tate boundary is bijective on Hom into a coefficient
which annihilates the smashed line and its first shift. -/
theorem bijective_precomp_tateSmashConnecting
    (X : PointedSimplicialPresheaf.{u + 1} (SmoothSite (Spec R)))
    (K : DerivedCategory (Sheaf Jᵣ AddCommGrpCat.{u + 1})) :
    let G := (uliftPointed.{u + 1, u} Cᵣ).obj (pointedTorus R)
    let N := reducedDerivedChains.{d, u + 1} Cᵣ Jᵣ
    Subsingleton (N.obj (Under.smash X A) ⟶ K) →
    Subsingleton ((N.obj (Under.smash X A))⟦(1 : ℤ)⟧ ⟶ K) →
    Function.Bijective (fun f : (N.obj (Under.smash X G))⟦(1 : ℤ)⟧ ⟶ K =>
      tateSmashConnecting R X ≫ f) := by
  intro G N h₀ h₁
  let h := (exists_tateSmashReducedCochains_shortExact R X).choose_spec
  let D := DerivedCategory.triangleOfSES h
  let T₀ := D.rotate
  have hT : T₀ ∈ distTriang _ :=
    rot_of_distTriang D (DerivedCategory.triangleOfSES_distinguished h)
  change Function.Bijective (fun f : T₀.obj₃ ⟶ K => T₀.mor₂ ≫ f)
  constructor
  · intro x y hxy
    change T₀.mor₂ ≫ x = T₀.mor₂ ≫ y at hxy
    apply sub_eq_zero.mp
    have hz : T₀.mor₂ ≫ (x - y) = 0 := by rw [Preadditive.comp_sub, hxy, sub_self]
    obtain ⟨g, hg⟩ := T₀.yoneda_exact₃ hT (x - y) hz
    exact hg.trans (by rw [h₁.elim g 0, comp_zero])
  · intro y
    obtain ⟨g, hg⟩ := T₀.yoneda_exact₂ hT y (h₀.elim _ _)
    exact ⟨g, hg.symm⟩

section Motivic

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{d}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "Rₖ" => CommRingCat.of k
local notation "Sₖ" => Spec Rₖ
local notation "Cₖ" => SmoothSite Sₖ
local notation "Jₖ" => SmoothSite.nisnevichTopology Sₖ
local notation "Qₖ" => toAffineLineHomotopyCategory Sₖ

omit [PerfectField k] in
/-- A represented reduced theory has trivial Hom groups on the
smashed pointed affine line by its explicit A¹-contraction. -/
theorem subsingleton_derivedHom_smashPointedAffineLine
    (K : CochainComplex (Sheaf Jₖ AddCommGrpCat.{u + 1}) ℤ) (n : ℤ)
    (E : AffineLineHomotopyCategory Sₖ)
    (e : ∀ Y : PointedSimplicialPresheaf.{u + 1} Cₖ, ((Qₖ).obj Y ⟶ E) ≃
      ((reducedDerivedChains.{d, u + 1} Cₖ Jₖ).obj Y ⟶ (DerivedCategory.Q.obj K)⟦n⟧))
    (X : PointedSimplicialPresheaf.{u + 1} Cₖ) :
    Subsingleton
      ((reducedDerivedChains.{d, u + 1} Cₖ Jₖ).obj
          (Under.smash X (liftedPointedAffineLine Rₖ)) ⟶
        (DerivedCategory.Q.obj K)⟦n⟧) := by
  let Y := Under.smash X (liftedPointedAffineLine Rₖ)
  let P := point.{u + 1} Cₖ
  let F := reducedDerivedChains.{d, u + 1} Cₖ Jₖ
  let : IsIso ((Qₖ).map (toPoint Cₖ Y)) :=
    isIso_toAffineLineHomotopyCategory_map_smashPointedAffineLineToPoint Rₖ X
  let b := asIso ((Qₖ).map (toPoint Cₖ Y))
  have hP : IsZero (F.obj P) :=
    DerivedCategory.Q.map_isZero (isZero_reducedCochains_obj_of_isZero Jₖ P (point_isZero Cₖ))
  let : Subsingleton (F.obj P ⟶ (DerivedCategory.Q.obj K)⟦n⟧) :=
    ⟨fun f g => hP.eq_of_src f g⟩
  exact ((e Y).symm.trans ((b.homCongr (Iso.refl E)).trans (e P))).injective.subsingleton

/-- Shift the source in a vanishing shifted Hom group. -/
theorem subsingleton_shiftedHom_of_subsingleton
    {D : Type*} [Category* D] [HasShift D ℤ] (K L : D) (n : ℤ)
    (h : Subsingleton (K ⟶ L⟦n - 1⟧)) :
    Subsingleton (K⟦(1 : ℤ)⟧ ⟶ L⟦n⟧) := by
  let e : (L⟦n - 1⟧)⟦(1 : ℤ)⟧ ≅ L⟦n⟧ :=
    ((shiftFunctorAdd' D (n - 1) 1 n (sub_add_cancel n 1)).app L).symm
  refine ⟨fun a b => (cancel_mono e.inv).1 ?_⟩
  let F := shiftFunctor D (1 : ℤ)
  obtain ⟨a₀, ha⟩ := F.map_surjective (a ≫ e.inv)
  obtain ⟨b₀, hb⟩ := F.map_surjective (b ≫ e.inv)
  exact ha.symm.trans ((F.congr_map (h.elim a₀ b₀)).trans hb)

/-- The Tate boundary is invertible in every integral reduced motivic cohomology group. -/
theorem bijective_precomp_tateSmashConnecting_integral
    (X : PointedSimplicialPresheaf.{u + 1} Cₖ) (n : ℤ) (q : ℕ) :
    Function.Bijective (fun f : ((reducedDerivedChains.{d, u + 1} Cₖ Jₖ).obj
        (Under.smash X ((uliftPointed.{u + 1, u} Cₖ).obj (pointedTorus Rₖ))))⟦(1 : ℤ)⟧ ⟶
          (DerivedCategory.Q.obj (motivicSheafComplex k q))⟦n⟧ =>
      tateSmashConnecting Rₖ X ≫ f) := by
  let K := motivicSheafComplex k q
  have h (i : ℤ) := subsingleton_derivedHom_smashPointedAffineLine k K i
    (motivicAffineLineRepresentative k i q) (motivicAffineLineRepresentativeHomEquiv k i q) X
  exact bijective_precomp_tateSmashConnecting Rₖ X _ (h n)
    (subsingleton_shiftedHom_of_subsingleton _ _ n (h (n - 1)))

/-- The same Tate boundary is invertible for the actual finite coefficient cone. -/
theorem bijective_precomp_tateSmashConnecting_finite
    (X : PointedSimplicialPresheaf.{u + 1} Cₖ) (n : ℤ) (q m : ℕ) :
    Function.Bijective (fun f : ((reducedDerivedChains.{d, u + 1} Cₖ Jₖ).obj
        (Under.smash X ((uliftPointed.{u + 1, u} Cₖ).obj (pointedTorus Rₖ))))⟦(1 : ℤ)⟧ ⟶
          (DerivedCategory.Q.obj (motivicFiniteSheafComplex k q m))⟦n⟧ =>
      tateSmashConnecting Rₖ X ≫ f) := by
  let K := motivicFiniteSheafComplex k q m
  have h (i : ℤ) := subsingleton_derivedHom_smashPointedAffineLine k K i
    (motivicFiniteAffineLineRepresentative k i q m)
    (motivicFiniteAffineLineRepresentativeHomEquiv k i q m) X
  exact bijective_precomp_tateSmashConnecting Rₖ X _ (h n)
    (subsingleton_shiftedHom_of_subsingleton _ _ n (h (n - 1)))

end Motivic

end AlgebraicGeometry.MotivicHomotopy
