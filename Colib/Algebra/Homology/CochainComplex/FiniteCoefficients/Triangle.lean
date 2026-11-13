/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Algebra.Homology.CochainComplex.FiniteCoefficients.Functoriality
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-!
# Maps and comparisons of the actual finite coefficient triangle

The triangle map is the native map of multiplication cones. Its
comparisons for an additive functor and a cochain shift retain
the same cone morphisms and the signs of the native triangle shift.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CochainComplex

namespace CochainComplex.finiteCoefficients

variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]

/-- The actual multiplication-cone map gives a morphism of the original triangles. -/
def triangleMap (n : ℕ) {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    triangle K n ⟶ triangle L n :=
  mappingCone.triangleMap (n • 𝟙 K) (n • 𝟙 L) f f (by simp)

@[simp]
theorem triangleMap_hom₁ (n : ℕ) {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    (triangleMap n f).hom₁ = f := rfl

@[simp]
theorem triangleMap_hom₂ (n : ℕ) {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    (triangleMap n f).hom₂ = f := rfl

@[simp]
theorem triangleMap_hom₃ (n : ℕ) {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    (triangleMap n f).hom₃ = map n f := rfl

/-- A zero map induces the zero map on both original cone coordinates. -/
theorem map_zero (n : ℕ) (K L : CochainComplex C ℤ) :
    map n (0 : K ⟶ L) = 0 := by
  apply HomologicalComplex.hom_ext
  intro i
  apply ext_to L n i
  · rw [map_a]
    exact (comp_zero (f := a K n i)).trans zero_comp.symm
  · rw [map_b]
    exact (comp_zero (f := b K n i)).trans zero_comp.symm

omit [HasBinaryBiproducts C] in
private theorem map_multiplication (K : CochainComplex C ℤ) (n : ℕ)
    {D : Type*} [Category* D] [Preadditive D]
    (F : CochainComplex C ℤ ⥤ D) [F.Additive] :
    F.map (n • 𝟙 K) = n • 𝟙 (F.obj K) :=
  (F.map_nsmul (f := 𝟙 K) (n := n)).trans (congrArg (n • ·) (F.map_id _))

private def mappingConeTriangleCongr {K L : CochainComplex C ℤ} {f g : K ⟶ L}
    (h : f = g) : mappingCone.triangle f ≅ mappingCone.triangle g :=
  eqToIso (congrArg mappingCone.triangle h)

private theorem mappingConeTriangleCongr_hom₃ {K L : CochainComplex C ℤ}
    {f g : K ⟶ L} (h : f = g) :
    (mappingConeTriangleCongr h).hom.hom₃ =
      (eqToIso (congrArg (fun a : K ⟶ L => mappingCone a) h)).hom := by
  subst g
  simp [mappingConeTriangleCongr]

private theorem mappingConeTriangleCongr_hom₁ {K L : CochainComplex C ℤ}
    {f g : K ⟶ L} (h : f = g) :
    (mappingConeTriangleCongr h).hom.hom₁ = 𝟙 K := by
  subst g
  simp [mappingConeTriangleCongr]

private theorem mappingConeTriangleCongr_hom₂ {K L : CochainComplex C ℤ}
    {f g : K ⟶ L} (h : f = g) :
    (mappingConeTriangleCongr h).hom.hom₂ = 𝟙 L := by
  subst g
  simp [mappingConeTriangleCongr]

variable {D : Type*} [Category* D] [Preadditive D] [HasBinaryBiproducts D]
  (F : C ⥤ D) [F.Additive]

/-- Applying an additive functor to the original multiplication triangle
uses its native cone comparison. -/
@[no_expose]
def mapTriangleIso (K : CochainComplex C ℤ) (n : ℕ) :
    let G := F.mapHomologicalComplex (.up ℤ)
    G.mapTriangle.obj (triangle K n) ≅ triangle (G.obj K) n :=
  let h := map_multiplication K n (F.mapHomologicalComplex (.up ℤ))
  mappingCone.mapTriangleIso (n • 𝟙 K) F ≪≫ mappingConeTriangleCongr h

/-- The third component is the actual additive comparison of multiplication cones. -/
theorem mapTriangleIso_hom₃ (K : CochainComplex C ℤ) (n : ℕ) :
    (mapTriangleIso F K n).hom.hom₃ = (mapIso F K n).hom := by
  unfold mapTriangleIso
  let h := map_multiplication K n (F.mapHomologicalComplex (.up ℤ))
  change (mappingCone.mapHomologicalComplexIso (n • 𝟙 K) F).hom ≫
      (mappingConeTriangleCongr h).hom.hom₃ = _
  rw [mappingConeTriangleCongr_hom₃, mapIso_eq F K n h]
  rfl

/-- The first integral component is the identity. -/
theorem mapTriangleIso_hom₁ (K : CochainComplex C ℤ) (n : ℕ) :
    (mapTriangleIso F K n).hom.hom₁ = 𝟙 _ := by
  unfold mapTriangleIso
  change 𝟙 _ ≫ (mappingConeTriangleCongr _).hom.hom₁ = _
  exact (Category.id_comp _).trans (mappingConeTriangleCongr_hom₁ _)

/-- The second integral component is the identity. -/
theorem mapTriangleIso_hom₂ (K : CochainComplex C ℤ) (n : ℕ) :
    (mapTriangleIso F K n).hom.hom₂ = 𝟙 _ := by
  unfold mapTriangleIso
  change 𝟙 _ ≫ (mappingConeTriangleCongr _).hom.hom₂ = _
  exact (Category.id_comp _).trans (mappingConeTriangleCongr_hom₂ _)

/-- The triangle shift and the native cone shift identify the original
finite coefficient triangle with that of the shifted coefficient. -/
@[no_expose]
def shiftTriangleIso (K : CochainComplex C ℤ) (n : ℕ) (s : ℤ) :
    (Triangle.shiftFunctor (CochainComplex C ℤ) s).obj (triangle K n) ≅
      triangle (K⟦s⟧) n := by
  let S : CochainComplex C ℤ ⥤ CochainComplex C ℤ := CategoryTheory.shiftFunctor _ s
  let h : S.map (n • 𝟙 K) = n • 𝟙 (S.obj K) :=
    (S.map_nsmul (f := 𝟙 K) (n := n)).trans (congrArg (n • ·) (S.map_id K))
  exact mappingCone.shiftTriangleIso (n • 𝟙 K) s ≪≫ mappingConeTriangleCongr h

/-- On the cone the triangle comparison is the native signed shift
followed by the actual scalar-multiplication transport. -/
theorem shiftTriangleIso_hom₃ (K : CochainComplex C ℤ) (n : ℕ) (s : ℤ) :
    ∀ h : ((n • 𝟙 K)⟦s⟧') = n • 𝟙 (K⟦s⟧),
    (shiftTriangleIso K n s).hom.hom₃ =
      (mappingCone.shiftIso (n • 𝟙 K) s).hom ≫
        (eqToIso (congrArg (fun a : K⟦s⟧ ⟶ K⟦s⟧ => mappingCone a) h)).hom := by
  intro h
  unfold shiftTriangleIso
  change (mappingCone.shiftIso (n • 𝟙 K) s).hom ≫ (mappingConeTriangleCongr h).hom.hom₃ = _
  rw [mappingConeTriangleCongr_hom₃]

/-- The first integral component is the identity under the native shift. -/
theorem shiftTriangleIso_hom₁ (K : CochainComplex C ℤ) (n : ℕ) (s : ℤ) :
    (shiftTriangleIso K n s).hom.hom₁ = 𝟙 (K⟦s⟧) := by
  unfold shiftTriangleIso
  change 𝟙 _ ≫ (mappingConeTriangleCongr _).hom.hom₁ = _
  exact (Category.id_comp _).trans (mappingConeTriangleCongr_hom₁ _)

/-- The second integral component retains the native triangle shift sign. -/
theorem shiftTriangleIso_hom₂ (K : CochainComplex C ℤ) (n : ℕ) (s : ℤ) :
    (shiftTriangleIso K n s).hom.hom₂ = s.negOnePow • 𝟙 (K⟦s⟧) := by
  unfold shiftTriangleIso
  change (s.negOnePow • 𝟙 _) ≫ (mappingConeTriangleCongr _).hom.hom₂ = _
  rw [mappingConeTriangleCongr_hom₂]
  exact Category.comp_id _

/-- The inverse additive comparison is the identity on the first integral term. -/
theorem mapTriangleIso_inv_hom₁ (K : CochainComplex C ℤ) (n : ℕ) :
    (mapTriangleIso F K n).inv.hom₁ = 𝟙 _ := by
  have h := (mapTriangleIso F K n).hom_inv_id_triangle_hom₁
  rw [mapTriangleIso_hom₁ F K n, Category.id_comp] at h
  exact h

/-- The inverse additive comparison is the identity on the second integral term. -/
theorem mapTriangleIso_inv_hom₂ (K : CochainComplex C ℤ) (n : ℕ) :
    (mapTriangleIso F K n).inv.hom₂ = 𝟙 _ := by
  have h := (mapTriangleIso F K n).hom_inv_id_triangle_hom₂
  rw [mapTriangleIso_hom₂ F K n, Category.id_comp] at h
  exact h

/-- The inverse additive comparison uses the same native cone isomorphism. -/
theorem mapTriangleIso_inv_hom₃ (K : CochainComplex C ℤ) (n : ℕ) :
    (mapTriangleIso F K n).inv.hom₃ = (mapIso F K n).inv := by
  let a := mapTriangleIso F K n
  let b := mapIso F K n
  have h : a.hom.hom₃ ≫ a.inv.hom₃ = 𝟙 _ := a.hom_inv_id_triangle_hom₃
  apply (cancel_epi b.hom).1
  exact ((congrArg (· ≫ a.inv.hom₃) (mapTriangleIso_hom₃ F K n).symm).trans h).trans
    b.hom_inv_id.symm

variable {F}

/-- The native cone comparison also commutes with transformations of the
coefficient functor, on both signed coordinates. -/
@[reassoc]
theorem mapIso_natTrans {G : C ⥤ D} [G.Additive] (τ : F ⟶ G)
    (K : CochainComplex C ℤ) (n : ℕ) :
    (mapIso F K n).hom ≫ map n ((τ.mapHomologicalComplex (.up ℤ)).app K) =
      (τ.mapHomologicalComplex (.up ℤ)).app (finiteCoefficients K n) ≫ (mapIso G K n).hom := by
  let c := ComplexShape.up ℤ
  let L := (F.mapHomologicalComplex c).obj K
  let M := (G.mapHomologicalComplex c).obj K
  let e := (mapIso F K n).hom
  let e' := (mapIso G K n).hom
  let g := (τ.mapHomologicalComplex c).app K
  let h := (τ.mapHomologicalComplex c).app (finiteCoefficients K n)
  apply HomologicalComplex.hom_ext
  intro i
  change e.f i ≫ (map n g).f i = h.f i ≫ e'.f i
  apply ext_to M n i
  · rw [Category.assoc, Category.assoc, map_a, mapIso_hom_a_assoc, mapIso_hom_a]
    exact τ.naturality (a K n i)
  · rw [Category.assoc, Category.assoc, map_b, mapIso_hom_b_assoc, mapIso_hom_b]
    exact τ.naturality (b K n i)

/-- The additive comparison for the identity functor is the original
identification of its termwise action with the identity. -/
theorem mapIso_id_comp_mapId (K : CochainComplex C ℤ) (n : ℕ) :
    (mapIso (𝟭 C) K n).hom ≫
        map n ((Functor.mapHomologicalComplexIdIso C (.up ℤ)).hom.app K) =
      (Functor.mapHomologicalComplexIdIso C (.up ℤ)).hom.app (finiteCoefficients K n) := by
  let j := Functor.mapHomologicalComplexIdIso C (.up ℤ)
  let e := (mapIso (𝟭 C) K n).hom
  let M := ((𝟭 C).mapHomologicalComplex (.up ℤ)).obj K
  apply HomologicalComplex.hom_ext
  intro i
  change e.f i ≫ (map n (j.hom.app K)).f i = 𝟙 _
  apply ext_to K n i
  · change (e.f i ≫ (map n (j.hom.app K)).f i) ≫ a K n i = 𝟙 _ ≫ a K n i
    have h : (map n (j.hom.app K)).f i ≫ a K n i =
        a M n i ≫ (j.hom.app K).f i :=
      map_a n (j.hom.app K) i
    rw [Category.assoc, h]
    change e.f i ≫ a _ n i ≫ 𝟙 _ = 𝟙 _ ≫ a K n i
    exact (mapIso_hom_a_assoc (𝟭 C) K n i (𝟙 _)).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  · change (e.f i ≫ (map n (j.hom.app K)).f i) ≫ b K n i = 𝟙 _ ≫ b K n i
    have h : (map n (j.hom.app K)).f i ≫ b K n i =
        b M n i ≫ (j.hom.app K).f (i + 1) :=
      map_b n (j.hom.app K) i
    rw [Category.assoc, h]
    change e.f i ≫ b _ n i ≫ 𝟙 _ = 𝟙 _ ≫ b K n i
    exact (mapIso_hom_b_assoc (𝟭 C) K n i (𝟙 _)).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- Finite coefficients retain the zero composite with an actual termwise
restriction, expressed in the original identity coordinates. -/
theorem map_comp_restriction {F : C ⥤ C} [F.Additive] (τ : F ⟶ 𝟭 C)
    {K L : CochainComplex C ℤ} (f : K ⟶ (F.mapHomologicalComplex (.up ℤ)).obj L)
    (n : ℕ)
    (h : f ≫ ((τ.mapHomologicalComplex (.up ℤ)).app L ≫
        (Functor.mapHomologicalComplexIdIso C (.up ℤ)).hom.app L) = 0) :
    map n f ≫ (mapIso F L n).inv ≫
        (τ.mapHomologicalComplex (.up ℤ)).app (finiteCoefficients L n) ≫
        (Functor.mapHomologicalComplexIdIso C (.up ℤ)).hom.app (finiteCoefficients L n) =
      0 := by
  let e := mapIso F L n
  let j := Functor.mapHomologicalComplexIdIso C (.up ℤ)
  let t := τ.mapHomologicalComplex (.up ℤ)
  have hr : e.inv ≫ t.app (finiteCoefficients L n) ≫ j.hom.app (finiteCoefficients L n) =
      map n (t.app L ≫ j.hom.app L) := by
    apply (cancel_epi e.hom).1
    calc
      _ = t.app (finiteCoefficients L n) ≫ j.hom.app (finiteCoefficients L n) :=
        e.hom_inv_id_assoc _
      _ = t.app (finiteCoefficients L n) ≫ (mapIso (𝟭 C) L n).hom ≫
          map n (j.hom.app L) := by rw [mapIso_id_comp_mapId]
      _ = (e.hom ≫ map n (t.app L)) ≫ map n (j.hom.app L) := by
        rw [← Category.assoc, ← mapIso_natTrans τ]
      _ = _ := by rw [Category.assoc, ← map_comp]
  change map n f ≫ (e.inv ≫ t.app (finiteCoefficients L n) ≫
    j.hom.app (finiteCoefficients L n)) = 0
  rw [hr, ← map_comp, h, map_zero]

/-- The inverse shift comparison is the identity on the first integral term. -/
theorem shiftTriangleIso_inv_hom₁ (K : CochainComplex C ℤ) (n : ℕ) (s : ℤ) :
    (shiftTriangleIso K n s).inv.hom₁ = 𝟙 (K⟦s⟧) := by
  let e := shiftTriangleIso K n s
  let f : K⟦s⟧ ⟶ K⟦s⟧ := e.hom.hom₁
  let g : K⟦s⟧ ⟶ K⟦s⟧ := e.inv.hom₁
  have h : f ≫ g = 𝟙 (K⟦s⟧) := e.hom_inv_id_triangle_hom₁
  have hf : f = 𝟙 (K⟦s⟧) := shiftTriangleIso_hom₁ K n s
  exact (Category.id_comp g).symm.trans ((congrArg (· ≫ g) hf.symm).trans h)

/-- The inverse shift by one has the same negative sign on the second integral term. -/
theorem shiftTriangleIso_inv_hom₂_one (K : CochainComplex C ℤ) (n : ℕ) :
    (shiftTriangleIso K n (1 : ℤ)).inv.hom₂ = -(𝟙 (K⟦(1 : ℤ)⟧)) := by
  let e := shiftTriangleIso K n (1 : ℤ)
  let L := K⟦(1 : ℤ)⟧
  let f : L ⟶ L := e.hom.hom₂
  let g : L ⟶ L := e.inv.hom₂
  have h : f ≫ g = 𝟙 L := e.hom_inv_id_triangle_hom₂
  have hf : f = -(𝟙 L) := by
    change (shiftTriangleIso K n (1 : ℤ)).hom.hom₂ = _
    rw [shiftTriangleIso_hom₂, Int.negOnePow_one, Units.neg_smul, one_smul]
  have h' : -g = 𝟙 L :=
    (congrArg Neg.neg (Category.id_comp g)).symm.trans
      ((Preadditive.neg_comp _ _).symm.trans ((congrArg (· ≫ g) hf.symm).trans h))
  exact neg_eq_iff_eq_neg.mp h'

end CochainComplex.finiteCoefficients
