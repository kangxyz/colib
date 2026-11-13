/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Algebra.Homology.CochainComplex.FiniteCoefficients.Triangle
public import Colib.Algebra.Homology.DerivedCategory.MapTriangleCommShift
public import Colib.Algebra.Homology.DerivedCategory.SplitTriangleLift
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.TatePowerDerivedBond
public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.Complex
public import Colib.AlgebraicGeometry.MotivicCohomology.TransferParameterUnit
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived.ReducedShift

/-!
# The original finite coefficient parameter triangle

The actual integral parameter map induces its native map of
multiplication cones. The shifted target triangle, the additive
torus reindexing, and the derived unit retain this exact third map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.Scheme CochainComplex

universe u w

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (SheafWithTransfers.{u + 1} k)]

local notation "B" => torusSectionsFunctor k
local notation "R" => torusSectionsDerivedFunctor k
local notation "η" => torusSectionsDerivedUnit k
local notation "Qₙ" =>
  (DerivedCategory.Q : CochainComplex (LargeSheaves k) ℤ ⥤ DerivedCategory (LargeSheaves k))

/-- Use the canonical abelian structure for the finite coefficient triangle. -/
local instance tatePowerFiniteBondAbelian : Abelian (SheafWithTransfers.{u + 1} k) :=
  SheafWithTransfers.abelian k

omit [HasDerivedCategory (LargeSheaves k)] in
/-- The original finite coefficient triangle for the next weight, shifted by one. -/
abbrev shiftedFiniteParameterTriangle (q n : ℕ) :
    Triangle (CochainComplex (LargeSheaves k) ℤ) :=
  (Triangle.shiftFunctor (CochainComplex (LargeSheaves k) ℤ) (1 : ℤ)).obj
    (motivicFiniteComplex.triangle k (q + 1) n)

omit [HasDerivedCategory (LargeSheaves k)] in
private def finiteParameterTriangleMap (q n : ℕ) :
    motivicFiniteComplex.triangle k q n ⟶
      ((B).mapHomologicalComplex (.up ℤ)).mapTriangle.obj
        (shiftedFiniteParameterTriangle k q n) := by
  let K := motivicComplex k (q + 1)
  let A := (B).mapHomologicalComplex (.up ℤ)
  let s := finiteCoefficients.shiftTriangleIso K n 1
  let t := finiteCoefficients.mapTriangleIso (B) (K⟦(1 : ℤ)⟧) n
  exact finiteCoefficients.triangleMap n (motivicTransferParameterProduct k q) ≫
    t.inv ≫ A.mapTriangle.map s.inv

omit [HasDerivedCategory (LargeSheaves k)] in
/-- The actual finite parameter map into reindexed cochains is the
native map of multiplication cones, followed by the native shift and
additive coefficient comparisons. -/
@[no_expose]
def motivicFiniteTransferParameterProduct (q n : ℕ) :
    motivicFiniteComplex k q n ⟶ ((B).mapHomologicalComplex (.up ℤ)).obj
      ((motivicFiniteComplex k (q + 1) n)⟦(1 : ℤ)⟧) :=
  (finiteParameterTriangleMap k q n).hom₃

omit [HasDerivedCategory (LargeSheaves k)] in
/-- The original finite parameter map becomes the map into the integral
target cone after the native shift and additive cone comparisons. -/
theorem motivicFiniteTransferParameterProduct_comp_target (q n : ℕ) :
    let K := motivicComplex k (q + 1)
    let A := (B).mapHomologicalComplex (.up ℤ)
    motivicFiniteTransferParameterProduct k q n ≫
      A.map (finiteCoefficients.shiftTriangleIso K n 1).hom.hom₃ ≫
      (finiteCoefficients.mapIso (B) (K⟦(1 : ℤ)⟧) n).hom =
    finiteCoefficients.map n (motivicTransferParameterProduct k q) := by
  intro K A
  let s := finiteCoefficients.shiftTriangleIso K n 1
  let t := finiteCoefficients.mapTriangleIso (B) (K⟦(1 : ℤ)⟧) n
  let g := finiteCoefficients.map n (motivicTransferParameterProduct k q)
  let z := (finiteCoefficients.mapIso (B) (K⟦(1 : ℤ)⟧) n).hom
  have hs : s.inv.hom₃ ≫ s.hom.hom₃ = 𝟙 _ := s.inv_hom_id_triangle_hom₃
  have ht : t.inv.hom₃ ≫ z = 𝟙 _ :=
    (congrArg (t.inv.hom₃ ≫ ·)
      (finiteCoefficients.mapTriangleIso_hom₃ (B) (K⟦(1 : ℤ)⟧) n).symm).trans
        t.inv_hom_id_triangle_hom₃
  have hA : A.map s.inv.hom₃ ≫ A.map s.hom.hom₃ = 𝟙 _ :=
    (A.map_comp _ _).symm.trans ((A.congr_map hs).trans (A.map_id _))
  unfold motivicFiniteTransferParameterProduct finiteParameterTriangleMap
  change (g ≫ t.inv.hom₃ ≫ A.map s.inv.hom₃) ≫ A.map s.hom.hom₃ ≫ z = g
  have h₁ : (A.map s.inv.hom₃ ≫ A.map s.hom.hom₃) ≫ z = z :=
    (congrArg (· ≫ z) hA).trans (Category.id_comp z)
  calc
    _ = g ≫ t.inv.hom₃ ≫ (A.map s.inv.hom₃ ≫ A.map s.hom.hom₃) ≫ z := by
      simp only [Category.assoc]
    _ = g ≫ t.inv.hom₃ ≫ z := congrArg (fun m => g ≫ t.inv.hom₃ ≫ m) h₁
    _ = g := (congrArg (g ≫ ·) ht).trans (Category.comp_id g)

/-- Localizing the actual finite map and applying the genuine derived
torus unit gives the original finite parameter bond on derived sheaves. -/
def motivicDerivedFiniteTransferParameterProduct (q n : ℕ) :
    (Qₙ).obj (motivicFiniteComplex k q n) ⟶
      (R).obj ((Qₙ).obj ((motivicFiniteComplex k (q + 1) n)⟦(1 : ℤ)⟧)) :=
  (Qₙ).map (motivicFiniteTransferParameterProduct k q n) ≫
    (η).app ((motivicFiniteComplex k (q + 1) n)⟦(1 : ℤ)⟧)

/-- The finite derived bond is the third component of the actual map
of distinguished multiplication triangles. -/
@[no_expose]
def motivicDerivedFiniteParameterTriangleMap (q n : ℕ) :
    (Qₙ).mapTriangle.obj (motivicFiniteComplex.triangle k q n) ⟶
      (R).mapTriangle.obj ((Qₙ).mapTriangle.obj (shiftedFiniteParameterTriangle k q n)) := by
  let C := CochainComplex (LargeSheaves k) ℤ
  let D := DerivedCategory (LargeSheaves k)
  let A : C ⥤ C := (B).mapHomologicalComplex (.up ℤ)
  let L : C ⥤ D := Qₙ
  let G : D ⥤ D := R
  let T : Triangle C := shiftedFiniteParameterTriangle k q n
  let τ : A ⋙ L ⟶ L ⋙ G := η
  let f : L.mapTriangle.obj (motivicFiniteComplex.triangle k q n) ⟶
      L.mapTriangle.obj (A.mapTriangle.obj T) :=
    L.mapTriangle.map (finiteParameterTriangleMap k q n)
  exact f ≫ τ.mapComposedTriangleHom T

/-- The third component is exactly localization of the signed finite cone map. -/
theorem motivicDerivedFiniteParameterTriangleMap_hom₃ (q n : ℕ) :
    (motivicDerivedFiniteParameterTriangleMap k q n).hom₃ =
      motivicDerivedFiniteTransferParameterProduct k q n := by
  unfold motivicDerivedFiniteParameterTriangleMap motivicDerivedFiniteTransferParameterProduct
    motivicFiniteTransferParameterProduct
  simp only [Pretriangulated.comp_hom₃, Functor.mapTriangle_map_hom₃,
    NatTrans.mapComposedTriangleHom_hom₃]
  rfl

/-- The first integral component is the original signed derived parameter map. -/
theorem motivicDerivedFiniteParameterTriangleMap_hom₁ (q n : ℕ) :
    (motivicDerivedFiniteParameterTriangleMap k q n).hom₁ =
      motivicDerivedTransferParameterProduct k q := by
  let A := (B).mapHomologicalComplex (.up ℤ)
  let K := motivicComplex k (q + 1)
  let z : motivicComplex k q ⟶ A.obj (K⟦(1 : ℤ)⟧) := motivicTransferParameterProduct k q
  have h : (finiteParameterTriangleMap k q n).hom₁ = z := by
    unfold finiteParameterTriangleMap
    rw [Pretriangulated.comp_hom₁, Pretriangulated.comp_hom₁, Functor.mapTriangle_map_hom₁,
      finiteCoefficients.triangleMap_hom₁, finiteCoefficients.mapTriangleIso_inv_hom₁,
      finiteCoefficients.shiftTriangleIso_inv_hom₁]
    change z ≫ 𝟙 _ ≫ A.map (𝟙 (K⟦(1 : ℤ)⟧)) = z
    rw [A.map_id, Category.id_comp, Category.comp_id]
  unfold motivicDerivedFiniteParameterTriangleMap motivicDerivedTransferParameterProduct
  rw [Pretriangulated.comp_hom₁, Functor.mapTriangle_map_hom₁,
    NatTrans.mapComposedTriangleHom_hom₁, h]
  rfl

/-- The second integral component retains the native triangle shift sign. -/
theorem motivicDerivedFiniteParameterTriangleMap_hom₂ (q n : ℕ) :
    (motivicDerivedFiniteParameterTriangleMap k q n).hom₂ =
      -(motivicDerivedTransferParameterProduct k q) := by
  let A := (B).mapHomologicalComplex (.up ℤ)
  let K := motivicComplex k (q + 1)
  let z : motivicComplex k q ⟶ A.obj (K⟦(1 : ℤ)⟧) := motivicTransferParameterProduct k q
  have h : (finiteParameterTriangleMap k q n).hom₂ = -z := by
    unfold finiteParameterTriangleMap
    rw [Pretriangulated.comp_hom₂, Pretriangulated.comp_hom₂, Functor.mapTriangle_map_hom₂,
      finiteCoefficients.triangleMap_hom₂, finiteCoefficients.mapTriangleIso_inv_hom₂,
      finiteCoefficients.shiftTriangleIso_inv_hom₂_one]
    change z ≫ 𝟙 _ ≫ A.map (-𝟙 (K⟦(1 : ℤ)⟧)) = -z
    simp only [A.map_neg, A.map_id, Preadditive.comp_neg, Category.comp_id]
  unfold motivicDerivedFiniteParameterTriangleMap motivicDerivedTransferParameterProduct
  rw [Pretriangulated.comp_hom₂, Functor.mapTriangle_map_hom₂,
    NatTrans.mapComposedTriangleHom_hom₂, h]
  change (Qₙ).map (-z) ≫ (η).app (K⟦(1 : ℤ)⟧) =
    -((Qₙ).map z ≫ (η).app (K⟦(1 : ℤ)⟧))
  rw [(Qₙ).map_neg, Preadditive.neg_comp]

omit [HasDerivedCategory (LargeSheaves k)] in
/-- The literal finite parameter map still has zero restriction to one. -/
theorem motivicFiniteTransferParameterProduct_comp_unit (q n : ℕ) :
    motivicFiniteTransferParameterProduct k q n ≫
      (torusSectionsComplexUnitRestriction k).app
        ((motivicFiniteComplex k (q + 1) n)⟦(1 : ℤ)⟧) = 0 := by
  let K := motivicComplex k (q + 1)
  let L := K⟦(1 : ℤ)⟧
  let M := (motivicFiniteComplex k (q + 1) n)⟦(1 : ℤ)⟧
  let F := (B).mapHomologicalComplex (.up ℤ)
  let f := motivicTransferParameterProduct k q
  let g := finiteCoefficients.map n f
  let a := (finiteCoefficients.shiftTriangleIso K n 1).inv.hom₃
  let b := (finiteCoefficients.mapTriangleIso (B) L n).inv.hom₃
  let r := torusSectionsComplexUnitRestriction k
  have hn : F.map a ≫ r.app M = r.app (finiteCoefficients L n) ≫ a := r.naturality a
  have hb : b = (finiteCoefficients.mapIso (B) L n).inv :=
    finiteCoefficients.mapTriangleIso_inv_hom₃ (B) L n
  have h : g ≫ b ≫ r.app (finiteCoefficients L n) = 0 := by
    rw [hb]
    exact finiteCoefficients.map_comp_restriction (torusSectionsUnitNatTrans k) f n
      (motivicTransferParameterProduct_comp_unit k q)
  unfold motivicFiniteTransferParameterProduct finiteParameterTriangleMap
  change (g ≫ b ≫ F.map a) ≫ r.app M = _
  calc
    _ = g ≫ b ≫ (F.map a ≫ r.app M) := by simp only [Category.assoc]
    _ = (g ≫ b ≫ r.app (finiteCoefficients L n)) ≫ a := by
      rw [hn]
      simp only [Category.assoc]
    _ = _ := by rw [h, zero_comp]

/-- The actual finite derived map lands in the kernel of the same unit restriction. -/
theorem motivicDerivedFiniteTransferParameterProduct_comp_unit (q n : ℕ) :
    motivicDerivedFiniteTransferParameterProduct k q n ≫
      (torusSectionsDerivedUnitRestriction k).app
        ((Qₙ).obj ((motivicFiniteComplex k (q + 1) n)⟦(1 : ℤ)⟧)) = 0 := by
  unfold motivicDerivedFiniteTransferParameterProduct
  rw [Category.assoc, torusSectionsDerivedUnitRestriction_app_Q_obj, ← (Qₙ).map_comp,
    motivicFiniteTransferParameterProduct_comp_unit, (Qₙ).map_zero]

private theorem projection_inclusion_comp_of_unit_zero
    {X K : DerivedCategory (LargeSheaves k)}
    (f : X ⟶ (R).obj K) (h : f ≫ (torusSectionsDerivedUnitRestriction k).app K = 0) :
    (f ≫ (reducedTorusSectionsDerivedProjection k).app K) ≫
        (reducedTorusSectionsDerivedInclusion k).app K = f := by
  rw [Category.assoc, reducedTorusSectionsDerivedProjection_inclusion,
    Preadditive.comp_sub, Category.comp_id, ← Category.assoc, h, zero_comp, sub_zero]

private theorem motivicDerivedTransferParameterProduct_comp_unit (q : ℕ) :
    motivicDerivedTransferParameterProduct k q ≫
      (torusSectionsDerivedUnitRestriction k).app
        ((Qₙ).obj ((motivicComplex k (q + 1))⟦(1 : ℤ)⟧)) = 0 := by
  unfold motivicDerivedTransferParameterProduct
  rw [Category.assoc, torusSectionsDerivedUnitRestriction_app_Q_obj, ← (Qₙ).map_comp,
    motivicTransferParameterProduct_comp_unit, (Qₙ).map_zero]

/-- The finite bond factors through the actual derived torus kernel. -/
def motivicDerivedReducedFiniteTransferParameterProduct (q n : ℕ) :
    (Qₙ).obj (motivicFiniteComplex k q n) ⟶
      (reducedTorusSectionsDerivedFunctor k).obj
        ((Qₙ).obj ((motivicFiniteComplex k (q + 1) n)⟦(1 : ℤ)⟧)) :=
  motivicDerivedFiniteTransferParameterProduct k q n ≫
    (reducedTorusSectionsDerivedProjection k).app _

/-- Including the reduced finite bond recovers the actual total bond. -/
theorem motivicDerivedReducedFiniteTransferParameterProduct_inclusion (q n : ℕ) :
    motivicDerivedReducedFiniteTransferParameterProduct k q n ≫
      (reducedTorusSectionsDerivedInclusion k).app _ =
    motivicDerivedFiniteTransferParameterProduct k q n :=
  projection_inclusion_comp_of_unit_zero k _
    (motivicDerivedFiniteTransferParameterProduct_comp_unit k q n)

private theorem derivedFiniteTriangle_distinguished (q n : ℕ) :
    (Qₙ).mapTriangle.obj (motivicFiniteComplex.triangle k q n) ∈
      distTriang (DerivedCategory (LargeSheaves k)) :=
  DerivedCategory.mappingCone_triangle_distinguished (n • 𝟙 (motivicComplex k q))

private theorem derivedShiftedFiniteTriangle_distinguished (q n : ℕ) :
    (Qₙ).mapTriangle.obj (shiftedFiniteParameterTriangle k q n) ∈
      distTriang (DerivedCategory (LargeSheaves k)) :=
  (Qₙ).mapTriangle_shift_distinguished 1 (motivicFiniteComplex.triangle k (q + 1) n)
    (derivedFiniteTriangle_distinguished k (q + 1) n)

set_option maxHeartbeats 450000 in
-- The cone, localization and reduced-kernel triangle presentations agree definitionally.
/-- Invertibility of the original reduced integral bond implies
invertibility of the original reduced finite bond on its actual cone. -/
theorem isIso_motivicDerivedReducedFiniteTransferParameterProduct
    (q n : ℕ)
    (h : IsIso (motivicDerivedTransferParameterProduct k q ≫
      (reducedTorusSectionsDerivedProjection k).app _)) :
    IsIso (motivicDerivedReducedFiniteTransferParameterProduct k q n) := by
  let D := DerivedCategory (LargeSheaves k)
  let U : Triangle D := (Qₙ).mapTriangle.obj (shiftedFiniteParameterTriangle k q n)
  let N := reducedTorusSectionsDerivedFunctor k
  let S : Triangle D := (Qₙ).mapTriangle.obj (motivicFiniteComplex.triangle k q n)
  let f : S ⟶ (R).mapTriangle.obj U := motivicDerivedFiniteParameterTriangleMap k q n
  let i : N.mapTriangle.obj U ⟶ (R).mapTriangle.obj U :=
    (reducedTorusSectionsDerivedInclusion k).mapTriangleHom U
  let p := reducedTorusSectionsDerivedProjection k
  let f₁ : S.obj₁ ⟶ (R).obj U.obj₁ := motivicDerivedTransferParameterProduct k q
  let f₂ : S.obj₂ ⟶ (R).obj U.obj₂ := motivicDerivedTransferParameterProduct k q
  let a : S.obj₁ ⟶ N.obj U.obj₁ := f₁ ≫ p.app U.obj₁
  let b : S.obj₂ ⟶ N.obj U.obj₂ := (-f₂) ≫ p.app U.obj₂
  let c : S.obj₃ ⟶ N.obj U.obj₃ := motivicDerivedReducedFiniteTransferParameterProduct k q n
  let : Mono i.hom₁ := inferInstanceAs
    (Mono (kernel.ι ((torusSectionsDerivedUnitRestriction k).app U.obj₁)))
  let : Mono i.hom₂ := inferInstanceAs
    (Mono (kernel.ι ((torusSectionsDerivedUnitRestriction k).app U.obj₂)))
  let : Mono i.hom₃ := inferInstanceAs
    (Mono (kernel.ι ((torusSectionsDerivedUnitRestriction k).app U.obj₃)))
  have ha : a ≫ i.hom₁ = f.hom₁ :=
    (projection_inclusion_comp_of_unit_zero k _
      (motivicDerivedTransferParameterProduct_comp_unit k q)).trans
        (motivicDerivedFiniteParameterTriangleMap_hom₁ k q n).symm
  have hb : b ≫ i.hom₂ = f.hom₂ := by
    let r := (torusSectionsDerivedUnitRestriction k).app U.obj₂
    have hz : f₂ ≫ r = 0 := motivicDerivedTransferParameterProduct_comp_unit k q
    have hz' : (-f₂) ≫ r = 0 :=
      (Preadditive.neg_comp _ _).trans ((congrArg Neg.neg hz).trans neg_zero)
    have h₂ : f.hom₂ = -f₂ := motivicDerivedFiniteParameterTriangleMap_hom₂ k q n
    exact (projection_inclusion_comp_of_unit_zero k (-f₂) hz').trans h₂.symm
  have hc : c ≫ i.hom₃ = f.hom₃ :=
    (motivicDerivedReducedFiniteTransferParameterProduct_inclusion k q n).trans
      (motivicDerivedFiniteParameterTriangleMap_hom₃ k q n).symm
  let g : S ⟶ N.mapTriangle.obj U := liftTriangleMorphism f i a b c ha hb hc
  have hS : S ∈ distTriang D := derivedFiniteTriangle_distinguished k q n
  have hU : U ∈ distTriang D := derivedShiftedFiniteTriangle_distinguished k q n
  have hN : N.mapTriangle.obj U ∈ distTriang D := N.map_distinguished U hU
  let a₂ : S.obj₂ ⟶ N.obj U.obj₂ := f₂ ≫ p.app U.obj₂
  let : IsIso a₂ := h
  have hb' : b = -a₂ := Preadditive.neg_comp _ _
  have hn : IsIso (-a₂) := (-asIso a₂).isIso_hom
  have hbIso : IsIso b := hb'.symm ▸ hn
  have haIso : IsIso a := h
  have hg₁ : g.hom₁ = a := rfl
  have hg₂ : g.hom₂ = b := rfl
  have hg₃ : g.hom₃ = c := rfl
  have hgIso : IsIso g.hom₃ :=
    isIso₃_of_isIso₁₂ g hS hN (hg₁.symm ▸ haIso) (hg₂.symm ▸ hbIso)
  change IsIso c
  exact hg₃ ▸ hgIso

end AlgebraicGeometry.MotivicHomotopy
