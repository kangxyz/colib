/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.GeometricMotives.Representability
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.ReflectionNaturality
import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.A1InvariantDerivedHom
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! # Affine-line invariance of smooth motives -/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry.Scheme SmoothSite.Contraction

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "S" => Spec (CommRingCat.of k)
local notation "NST" => LargeSheaves k
local notation "V" => DerivedCategory.Minus.ι (C := NST)
local notation "J" => effectiveMotivesMinusToDerived k

set_option backward.isDefEq.respectTransparency false in
/-- The derived comparison preserves precomposition by any signed correspondence. -/
theorem effectiveMotiveDerivedHomEquiv_precomp {X Y : Cor k} (f : X ⟶ Y)
    {K : EffectiveMotivesMinus k} (g : (effectiveMotive k).obj Y ⟶ K) :
    effectiveMotiveDerivedHomEquiv k X K ((effectiveMotive k).map f ≫ g) =
      (DerivedCategory.singleFunctor NST 0).map ((transferRepresentable k).map f) ≫
        effectiveMotiveDerivedHomEquiv k Y K g := by
  let L := effectiveReflection k
  let R := transferRepresentable k
  let s := singleTransferSheafMinus k
  let e (U : Cor k) : L.obj (s.obj (R.obj U)) ≅ (effectiveMotive k).obj U :=
    singleSheafReflectionIso k ((representableLarge k).obj U)
  let b := s.map (R.map f)
  let d (U : Cor k) := (DerivedCategory.singleFunctorIsoCompQ NST 0).app (R.obj U)
  let r := (DerivedCategory.singleFunctor NST 0).map (R.map f)
  let a := effectiveReflectionAdjunction k
  have h : L.map b ≫ (e Y).hom = (e X).hom ≫ (effectiveMotive k).map f :=
    singleSheafReflectionIso_naturality k ((representableLarge k).map f)
  have hd : r ≫ (d Y).hom = (d X).hom ≫ (V).map b :=
    (DerivedCategory.singleFunctorIsoCompQ NST 0).hom.naturality (R.map f)
  have he : (e X).hom ≫ ((effectiveMotive k).map f ≫ g) =
      L.map b ≫ ((e Y).hom ≫ g) := by
    rw [← Category.assoc, ← h, Category.assoc]
  change (d X).hom ≫ (V).map (a.homEquiv (s.obj (R.obj X)) K
    ((e X).hom ≫ ((effectiveMotive k).map f ≫ g))) =
      r ≫ ((d Y).hom ≫ (V).map (a.homEquiv (s.obj (R.obj Y)) K ((e Y).hom ≫ g)))
  rw [he, a.homEquiv_naturality_left, (V).map_comp, ← Category.assoc r, hd, Category.assoc]

private theorem bijective_precomp_of_target_iso {C : Type*} [Category C]
    {X Y A B : C} (r : X ⟶ Y) (e : A ≅ B)
    (h : Function.Bijective (fun f : Y ⟶ A => r ≫ f)) :
    Function.Bijective (fun f : Y ⟶ B => r ≫ f) := by
  let iX := e.homToEquiv (Z := X)
  let iY := e.homToEquiv (Z := Y)
  have hb := iX.bijective.comp (h.comp iY.symm.bijective)
  have he : (fun f : Y ⟶ B => r ≫ f) =
      (iX : (X ⟶ A) → (X ⟶ B)) ∘ ((fun f : Y ⟶ A => r ≫ f) ∘ iY.symm) := by
    funext f
    change r ≫ f = (r ≫ (f ≫ e.inv)) ≫ e.hom
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact he.symm ▸ hb

omit [HasDerivedCategory (PresheafWithTransfers.{u + 1} k)] in
private theorem bijective_precomp_of_derived_projection (X : SmoothSite S)
    (K : EffectiveMotivesMinus k) :
    let Y := affineLineCylinder.obj X
    let f : Cor.mk Y ⟶ Cor.mk X := (Cor.graphFunctor k).map
      ((projection (SmoothSite.additiveGroupObject S)).app X)
    let r := (DerivedCategory.singleFunctor NST 0).map ((transferRepresentable k).map f)
    Function.Bijective (fun a : (DerivedCategory.singleFunctor NST 0).obj
      ((transferRepresentable k).obj (Cor.mk X)) ⟶ (J).obj K => r ≫ a) := by
  dsimp only
  obtain ⟨b, hb⟩ := K.obj.property
  let E := (J).obj K
  have he : E.IsLE b := hb
  have hi := isIso_transferDerivedHomPresheaf_projection k X E b he
    (fun q => effectiveMotivesMinusCohomology_isA1Invariant k K q) 0
  apply bijective_precomp_of_target_iso _ ((shiftFunctorZero (DerivedCategory NST) ℤ).app E)
  exact (ConcreteCategory.isIso_iff_bijective _).1 hi

private theorem isIso_map_of_precomp_comparison {C D E : Type*}
    [Category C] [Category D] [Category E] (F : C ⥤ D) (H : C ⥤ E) (J' : D ⥤ E)
    {X Y : C} (f : X ⟶ Y) (e : ∀ (A : C) (K : D), (F.obj A ⟶ K) ≃ (H.obj A ⟶ J'.obj K))
    (hn : ∀ (K : D) (g : F.obj Y ⟶ K), e X K (F.map f ≫ g) = H.map f ≫ e Y K g)
    (hi : ∀ (K : D), Function.Bijective (fun g : H.obj Y ⟶ J'.obj K => H.map f ≫ g)) :
    IsIso (F.map f) := by
  apply isIso_of_coyoneda_map_bijective
  intro K
  let p (g : F.obj Y ⟶ K) := F.map f ≫ g
  have h : (e X K : _ → _) ∘ p = (fun g => H.map f ≫ g) ∘ (e Y K : _ → _) := funext (hn K)
  exact (Function.Bijective.of_comp_iff' (e X K).bijective p).1
    (h.symm ▸ ((hi K).comp (e Y K).bijective))

/-- The actual affine-line projection becomes invertible on smooth motives. -/
theorem isIso_effectiveSmoothMotive_affineLineProjection (X : SmoothSite S) :
    IsIso ((effectiveSmoothMotive k).map
      ((projection (SmoothSite.additiveGroupObject S)).app X)) := by
  let Y := affineLineCylinder.obj X
  let f : Cor.mk Y ⟶ Cor.mk X := (Cor.graphFunctor k).map
    ((projection (SmoothSite.additiveGroupObject S)).app X)
  change IsIso ((effectiveMotive k).map f)
  exact isIso_map_of_precomp_comparison (effectiveMotive k)
    (transferRepresentable k ⋙ DerivedCategory.singleFunctor NST 0) (J) f
    (fun U K => (effectiveMotiveDerivedHomEquiv k U K).toEquiv)
    (fun _ g => effectiveMotiveDerivedHomEquiv_precomp k f g)
    (bijective_precomp_of_derived_projection k X)

end AlgebraicGeometry.MotivicHomotopy
