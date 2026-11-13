/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Algebra.Homology.CochainComplex.FiniteCoefficients.Basic

/-!
# Mapping the original finite coefficient cone

An additive functor takes the multiplication cone to the same
multiplication cone on the image. Its natural comparison preserves
both signed coordinates and therefore identifies the original maps
of cones.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CochainComplex

namespace CochainComplex.finiteCoefficients

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]
  (F : C ⥤ D) [F.Additive]

local notation "R" => F.mapHomologicalComplex (ComplexShape.up ℤ)

omit [HasBinaryBiproducts C] [HasBinaryBiproducts D] in
private theorem map_multiplication (K : CochainComplex C ℤ) (n : ℕ) :
    (R).map (n • 𝟙 K) = n • 𝟙 ((R).obj K) :=
  ((R).map_nsmul (f := 𝟙 K) (n := n)).trans
    (congrArg (n • ·) ((R).map_id K))

/-- The canonical comparison for an additive functor applied to the
actual multiplication cone. -/
@[no_expose]
def mapIso (K : CochainComplex C ℤ) (n : ℕ) :
    (R).obj (finiteCoefficients K n) ≅ finiteCoefficients ((R).obj K) n :=
  mappingCone.mapHomologicalComplexIso (n • 𝟙 K) F ≪≫
    eqToIso (congrArg (fun f => mappingCone f) (map_multiplication F K n))

private theorem compare_coordinates (K : CochainComplex C ℤ) (n : ℕ) (i : ℤ) :
    ((mapIso F K n).hom.f i ≫ a ((R).obj K) n i = F.map (a K n i)) ∧
      ((mapIso F K n).hom.f i ≫ b ((R).obj K) n i = F.map (b K n i)) := by
  let L := (R).obj K
  let x := n • 𝟙 K
  let y := n • 𝟙 L
  let h : (R).map x = y := map_multiplication F K n
  have h₁ : (mappingCone.mapHomologicalComplexIso x F).hom.f i ≫
      (mappingCone.snd ((R).map x)).v i i (add_zero i) =
      F.map ((mappingCone.snd x).v i i (add_zero i)) := by
    change (mappingCone.mapHomologicalComplexXIso x F i).hom ≫ _ = _
    rw [mappingCone.mapHomologicalComplexXIso_eq x F i (i + 1) rfl]
    simp only [mappingCone.mapHomologicalComplexXIso'_hom, Preadditive.add_comp, Category.assoc,
      mappingCone.inl_v_snd_v, mappingCone.inr_f_snd_v, comp_zero, zero_add]
    exact Category.comp_id (F.map ((mappingCone.snd x).v i i (add_zero i)))
  have h₂ : (mappingCone.mapHomologicalComplexIso x F).hom.f i ≫
      (-(mappingCone.fst ((R).map x)).1.v i (i + 1) rfl) =
      F.map (-(mappingCone.fst x).1.v i (i + 1) rfl) := by
    change (mappingCone.mapHomologicalComplexXIso x F i).hom ≫ _ = _
    rw [mappingCone.mapHomologicalComplexXIso_eq x F i (i + 1) rfl]
    let g := F.map ((mappingCone.fst x).1.v i (i + 1) rfl)
    let p := F.map ((mappingCone.snd x).v i i (add_zero i))
    let u := (mappingCone.inl ((R).map x)).v (i + 1) i (by omega)
    let v := (mappingCone.inr ((R).map x)).f i
    let w := (mappingCone.fst ((R).map x)).1.v i (i + 1) rfl
    have hu : u ≫ w = 𝟙 (((R).obj K).X (i + 1)) :=
      mappingCone.inl_v_fst_v ((R).map x) (i + 1) i rfl
    have hv : v ≫ w = 0 := mappingCone.inr_f_fst_v ((R).map x) i (i + 1) rfl
    have hsum : (g ≫ u + p ≫ v) ≫ w = g := by
      rw [Preadditive.add_comp, Category.assoc, Category.assoc, hu, hv, comp_zero, add_zero]
      exact Category.comp_id g
    change (g ≫ u + p ≫ v) ≫ (-w) = F.map (-(mappingCone.fst x).1.v i (i + 1) rfl)
    calc
      _ = -((g ≫ u + p ≫ v) ≫ w) := Preadditive.comp_neg _ _
      _ = -g := congrArg Neg.neg hsum
      _ = _ := F.map_neg.symm
  have he {f g : L ⟶ L} (hfg : f = g) :
      ((eqToIso (congrArg (fun m => mappingCone m) hfg)).hom.f i ≫
          (mappingCone.snd g).v i i (add_zero i) = (mappingCone.snd f).v i i (add_zero i)) ∧
        ((eqToIso (congrArg (fun m => mappingCone m) hfg)).hom.f i ≫
          (-(mappingCone.fst g).1.v i (i + 1) rfl) = -(mappingCone.fst f).1.v i (i + 1) rfl) := by
    subst g
    simp
  let m := (mappingCone.mapHomologicalComplexIso x F).hom.f i
  let e := (eqToIso (congrArg (fun f => mappingCone f) h)).hom.f i
  constructor
  · change (m ≫ e) ≫ (mappingCone.snd y).v i i (add_zero i) = _
    exact (Category.assoc _ _ _).trans ((congrArg (m ≫ ·) (he h).1).trans h₁)
  · change (m ≫ e) ≫ (-(mappingCone.fst y).1.v i (i + 1) rfl) = _
    exact (Category.assoc _ _ _).trans ((congrArg (m ≫ ·) (he h).2).trans h₂)

/-- The comparison uses the original additive mapping-cone isomorphism
and transport along the scalar multiplication equation. -/
theorem mapIso_eq (K : CochainComplex C ℤ) (n : ℕ)
    (h : (R).map (n • 𝟙 K) = n • 𝟙 ((R).obj K)) :
    mapIso F K n = mappingCone.mapHomologicalComplexIso (n • 𝟙 K) F ≪≫
      eqToIso (congrArg (fun f => mappingCone f) h) := by
  unfold mapIso
  rfl

/-- The integral coordinate is the original coordinate after applying the functor. -/
@[reassoc]
theorem mapIso_hom_a (K : CochainComplex C ℤ) (n : ℕ) (i : ℤ) :
    (mapIso F K n).hom.f i ≫ a ((R).obj K) n i = F.map (a K n i) :=
  (compare_coordinates F K n i).1

/-- The positive Bockstein coordinate retains its sign. -/
@[reassoc]
theorem mapIso_hom_b (K : CochainComplex C ℤ) (n : ℕ) (i : ℤ) :
    (mapIso F K n).hom.f i ≫ b ((R).obj K) n i = F.map (b K n i) :=
  (compare_coordinates F K n i).2

/-- The additive functor comparison preserves the actual maps of multiplication cones. -/
@[reassoc]
theorem mapIso_naturality {K L : CochainComplex C ℤ} (f : K ⟶ L) (n : ℕ) :
    (R).map (map n f) ≫ (mapIso F L n).hom =
      (mapIso F K n).hom ≫ map n ((R).map f) := by
  ext i : 1
  let a' := ((R).map (map n f)).f i
  let x := (mapIso F K n).hom.f i
  let y := (mapIso F L n).hom.f i
  let f' := (map n ((R).map f)).f i
  change a' ≫ y = x ≫ f'
  have ha : (a' ≫ y) ≫ a ((R).obj L) n i =
      (x ≫ f') ≫ a ((R).obj L) n i := by
    change (F.map ((map n f).f i) ≫ y) ≫ a ((R).obj L) n i = _
    rw [Category.assoc, mapIso_hom_a, ← F.map_comp, map_a, F.map_comp]
    change _ = (x ≫ f') ≫ a ((R).obj L) n i
    rw [Category.assoc, map_a]
    exact (mapIso_hom_a_assoc F K n i (F.map (f.f i))).symm
  have hb : (a' ≫ y) ≫ b ((R).obj L) n i =
      (x ≫ f') ≫ b ((R).obj L) n i := by
    change (F.map ((map n f).f i) ≫ y) ≫ b ((R).obj L) n i = _
    rw [Category.assoc, mapIso_hom_b, ← F.map_comp, map_b, F.map_comp]
    change _ = (x ≫ f') ≫ b ((R).obj L) n i
    rw [Category.assoc, map_b]
    exact (mapIso_hom_b_assoc F K n i (F.map (f.f (i + 1)))).symm
  refine mappingCone.ext_to (n • 𝟙 ((R).obj L)) i (i + 1) rfl ?_ ha
  apply neg_injective
  simpa only [b, Preadditive.comp_neg] using hb

end CochainComplex.finiteCoefficients
