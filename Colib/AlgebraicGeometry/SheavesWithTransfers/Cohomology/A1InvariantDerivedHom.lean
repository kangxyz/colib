/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.FiniteDimension
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.StrictA1.TransferExt
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.ObjectProperty
import Colib.CategoryTheory.Sites.Hypercohomology.FiniteWindow
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Triangulated.Yoneda
import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowNaturalTransformations
import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle

/-!
# A¹-invariance of derived Hom from smooth transfer representables

Strict A¹-invariance applies first to sheaves in degree zero. For a
bounded-above complex, the finite projective dimensions of the two
representables in a projection give a common cohomological cutoff.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry.Scheme SmoothSite.Contraction
open Stacks.Cohomology.FreeYonedaUnivLE

universe u v w

namespace AlgebraicGeometry.SheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (SheafWithTransfers.{u + 1} k)]

local notation "S" => Spec (CommRingCat.of k)
local notation "R" => transferRepresentable k
local notation "D₀" => DerivedCategory.singleFunctor _ 0
local notation "π" => projection (SmoothSite.additiveGroupObject S)

/-- Shifted Hom from the original Nisnevich transfer representables,
with the original action of finite correspondences by precomposition. -/
def transferDerivedHomPresheaf (p : ℤ) :
    DerivedCategory (SheafWithTransfers.{u + 1} k) ⥤ (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{w} :=
  shiftFunctor _ p ⋙ Functor.flip ((R ⋙ D₀).op ⋙ preadditiveCoyoneda)

private theorem exists_derivedPrecompositionProperty {Z : Type*} [Category* Z] [Abelian Z]
    [HasDerivedCategory.{w} Z] {X Y : DerivedCategory Z} (s : X ⟶ Y) :
    ∃ P : ObjectProperty (DerivedCategory Z),
      P.IsTriangulated ∧ P.IsClosedUnderIsomorphisms ∧
        ∀ E, P E ↔ ∀ p : ℤ, IsIso ((preadditiveYoneda.obj (E⟦p⟧)).map s.op) := by
  obtain ⟨W, g, δ, hT⟩ := Pretriangulated.distinguished_cocone_triangle s.op
  let T := Triangle.mk s.op g δ
  let P := (preadditiveCoyoneda.obj W).homologicalKernel
  refine ⟨P, inferInstance, inferInstance, fun E => ?_⟩
  let F := preadditiveYoneda.obj E
  have h₁ := F.homologicalKernel.trW_iff_of_distinguished T hT
  have h₂ := F.mem_homologicalKernel_trW_iff s.op
  exact (F.mem_homologicalKernel_iff W).symm.trans (h₁.symm.trans h₂)

private theorem exists_restrictionProperty {X Y : Cor k} (a : X ⟶ Y) :
    ∃ P : ObjectProperty (DerivedCategory (SheafWithTransfers.{u + 1} k)),
      P.IsTriangulated ∧ P.IsClosedUnderIsomorphisms ∧
        ∀ E, P E ↔ ∀ p : ℤ, IsIso (((transferDerivedHomPresheaf k p).obj E).map a.op) := by
  let Z := SheafWithTransfers.{u + 1} k
  exact exists_derivedPrecompositionProperty ((DerivedCategory.singleFunctor Z 0).map ((R).map a))

private theorem bijective_derivedPrecomp_of_ext {Z : Type*} [Category* Z] [Abelian Z]
    [HasDerivedCategory.{w} Z] [HasExt.{v} Z] {X Y F : Z} (a : X ⟶ Y) (n : ℕ)
    (h : Function.Bijective (fun x : Ext.{v} Y F n => (Ext.mk₀ a).comp x (zero_add n))) :
    Function.Bijective (fun x :
      (DerivedCategory.singleFunctor Z 0).obj Y ⟶
        (DerivedCategory.singleFunctor Z 0).obj F⟦(n : ℤ)⟧ =>
        (DerivedCategory.singleFunctor Z 0).map a ≫ x) := by
  let eX : Ext.{v} X F n ≃ _ := Ext.homEquiv
  let eY : Ext.{v} Y F n ≃ _ := Ext.homEquiv
  let f (x : Ext.{v} Y F n) := (Ext.mk₀ a).comp x (zero_add n)
  let g (x : (DerivedCategory.singleFunctor Z 0).obj Y ⟶
      (DerivedCategory.singleFunctor Z 0).obj F⟦(n : ℤ)⟧) :=
    (DerivedCategory.singleFunctor Z 0).map a ≫ x
  have hc : g ∘ eY = eX ∘ f := by
    funext x
    change (DerivedCategory.singleFunctor Z 0).map a ≫ x.hom = (f x).hom
    unfold f
    rw [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp]
  apply (Function.Bijective.of_comp_iff g eY.bijective).1
  rw [hc]
  exact eX.bijective.comp h

variable [PerfectField k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1})]

private theorem isIso_projection_single (X : SmoothSite S) (F : SheafWithTransfers.{u + 1} k)
    (hF : F.obj.IsA1Invariant) (p : ℤ) :
    IsIso (((transferDerivedHomPresheaf k p).obj ((D₀).obj F)).map
      ((Cor.graphFunctor k).map ((π).app X)).op) := by
  let Y := affineLineCylinder.obj X
  let f : Y ⟶ X := (π).app X
  let a : Cor.mk Y ⟶ Cor.mk X := (Cor.graphFunctor k).map f
  by_cases hp : 0 ≤ p
  · let n := p.toNat
    have hn : (n : ℤ) = p := Int.toNat_of_nonneg hp
    rw [← hn]
    let : HasExt.{u + 1} (SheafWithTransfers.{u + 1} k) := hasExt_of_enoughInjectives _
    exact (ConcreteCategory.isIso_iff_bijective _).2
      (bijective_derivedPrecomp_of_ext (F := F) ((R).map a) n
        ((ConcreteCategory.isIso_iff_bijective _).1 (isIso_transferExt_projection k X F hF n)))
  · let E := (D₀).obj F
    let : (E⟦p⟧).IsGE (-p) :=
      DerivedCategory.TStructure.t.isGE_shift E 0 p (-p) (by omega)
    have hZero (Z : Cor k) : Subsingleton ((D₀).obj ((R).obj Z) ⟶ E⟦p⟧) := by
      refine subsingleton_of_forall_eq 0 fun z => ?_
      exact DerivedCategory.TStructure.t.zero z 0 (-p) (by omega)
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact ⟨fun _ _ _ => (hZero (Cor.mk X)).elim _ _,
      fun z => ⟨0, (hZero (Cor.mk Y)).elim _ _⟩⟩

private theorem isIso_projection_of_bounded (X : SmoothSite S)
    (K : DerivedCategory (SheafWithTransfers.{u + 1} k)) (a : ℤ) (n : ℕ)
    (hGE : K.IsGE a) (hLE : K.IsLE (a + (n : ℤ)))
    (h : ∀ q, a ≤ q → q ≤ a + (n : ℤ) →
      ((DerivedCategory.homologyFunctor (SheafWithTransfers.{u + 1} k) q).obj K).obj.IsA1Invariant)
    (p : ℤ) :
    IsIso (((transferDerivedHomPresheaf k p).obj K).map
      ((Cor.graphFunctor k).map ((π).app X)).op) := by
  let f : Cor.mk (affineLineCylinder.obj X) ⟶ Cor.mk X :=
    (Cor.graphFunctor k).map ((π).app X)
  obtain ⟨P, hP, hClosed, hEquiv⟩ := exists_restrictionProperty k f
  let : P.IsTriangulated := hP
  let : P.IsClosedUnderIsomorphisms := hClosed
  have hK : P K := P.prop_of_isGE_of_isLE a n K hGE hLE (fun q hq₁ hq₂ =>
    (hEquiv _).mpr fun j => isIso_projection_single k X _ (h q hq₁ hq₂) j)
  exact (hEquiv K).mp hK p

/-- On a bounded-above object with A¹-invariant cohomology sheaves, the
original affine projection acts invertibly on shifted transfer Hom. -/
theorem isIso_transferDerivedHomPresheaf_projection (X : SmoothSite S)
    (K : DerivedCategory (SheafWithTransfers.{u + 1} k)) (b : ℤ) (hK : K.IsLE b)
    (h : ∀ q, ((DerivedCategory.homologyFunctor
      (SheafWithTransfers.{u + 1} k) q).obj K).obj.IsA1Invariant) (p : ℤ) :
    IsIso (((transferDerivedHomPresheaf k p).obj K).map
      ((Cor.graphFunctor k).map ((π).app X)).op) := by
  let Y := affineLineCylinder.obj X
  let f : Cor.mk Y ⟶ Cor.mk X := (Cor.graphFunctor k).map ((π).app X)
  obtain ⟨dx, hx⟩ := exists_transferRepresentable_hasProjectiveDimensionLE k X
  obtain ⟨dy, hy⟩ := exists_transferRepresentable_hasProjectiveDimensionLE k Y
  let : HasProjectiveDimensionLE ((R).obj (Cor.mk X)) dx := hx
  let : HasProjectiveDimensionLE ((R).obj (Cor.mk Y)) dy := hy
  let d := max dx dy
  let : HasProjectiveDimensionLE ((R).obj (Cor.mk X)) d :=
    hasProjectiveDimensionLT_of_ge _ (dx + 1) (d + 1) (by dsimp [d]; omega)
  let : HasProjectiveDimensionLE ((R).obj (Cor.mk Y)) d :=
    hasProjectiveDimensionLT_of_ge _ (dy + 1) (d + 1) (by dsimp [d]; omega)
  let a : ℤ := p - (d : ℤ)
  let B := max b a
  let t := DerivedCategory.TStructure.t (C := SheafWithTransfers.{u + 1} k)
  let L := (t.truncGE a).obj K
  let r := (t.truncGEπ a).app K
  have hGE : L.IsGE a := inferInstanceAs (((t.truncGE a).obj K).IsGE a)
  have hLE : L.IsLE B := (DerivedCategory.isLE_iff L B).mpr fun q hq => by
    let H := DerivedCategory.homologyFunctor (SheafWithTransfers.{u + 1} k) q
    let : IsIso (H.map r) :=
      DerivedCategory.isIso_homologyMap_truncGEπ_app a q (by dsimp [B] at hq; omega) K
    exact (asIso (H.map r)).isZero_iff.mp
      ((DerivedCategory.isLE_iff K b).mp hK q (by dsimp [B] at hq; omega))
  have hB : a + ((B - a).toNat : ℤ) = B := by dsimp [B]; omega
  let F := transferDerivedHomPresheaf k p
  let : IsIso ((F.obj L).map f.op) :=
    isIso_projection_of_bounded k X L a (B - a).toNat hGE
      (by simpa only [hB] using hLE) (fun q hq _ => by
        let : IsIso ((DerivedCategory.homologyFunctor (SheafWithTransfers.{u + 1} k) q).map r) :=
          DerivedCategory.isIso_homologyMap_truncGEπ_app a q hq K
        exact PresheafWithTransfers.IsA1Invariant.of_iso (h q) ((forget k).mapIso
          (asIso ((DerivedCategory.homologyFunctor (SheafWithTransfers.{u + 1} k) q).map r)))) p
  let η : F.obj K ⟶ F.obj L := F.map r
  let : IsIso (η.app (op (Cor.mk X))) := (ConcreteCategory.isIso_iff_bijective _).mpr
    (DerivedCategory.bijective_comp_truncGEπ_of_hasProjectiveDimensionLE
      ((R).obj (Cor.mk X)) d K p)
  let : IsIso (η.app (op (Cor.mk Y))) := (ConcreteCategory.isIso_iff_bijective _).mpr
    (DerivedCategory.bijective_comp_truncGEπ_of_hasProjectiveDimensionLE
      ((R).obj (Cor.mk Y)) d K p)
  have : IsIso ((F.obj K).map f.op ≫ η.app (op (Cor.mk Y))) := by
    rw [η.naturality f.op]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (η.app (op (Cor.mk Y)))

end AlgebraicGeometry.SheafWithTransfers
