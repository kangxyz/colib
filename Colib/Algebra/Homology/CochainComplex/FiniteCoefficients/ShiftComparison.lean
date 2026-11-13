/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Algebra.Homology.CochainComplex.FiniteCoefficients.Triangle

/-!
# Signed shift and additive comparison of finite coefficients

The cone isomorphism in the shift of the original coefficient triangle
commutes with the additive cone comparison. Its integral coordinate
is unchanged and its positive Bockstein coordinate changes sign.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CochainComplex.HomComplex

namespace CochainComplex.finiteCoefficients

variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]

/-- The third component of the original finite coefficient triangle shifted by one. -/
abbrev shiftOneIso (K : CochainComplex C ℤ) (n : ℕ) :
    (finiteCoefficients K n)⟦(1 : ℤ)⟧ ≅ finiteCoefficients (K⟦(1 : ℤ)⟧) n :=
  Triangle.π₃.mapIso (shiftTriangleIso K n 1)

private theorem transport_hom_coordinates {K : CochainComplex C ℤ} {f g : K ⟶ K}
    (h : f = g) (i : ℤ) :
    let e := eqToIso (congrArg (fun f : K ⟶ K => mappingCone f) h)
    (e.hom.f i ≫ (mappingCone.snd g).v i i (add_zero i) =
        (mappingCone.snd f).v i i (add_zero i)) ∧
    (e.hom.f i ≫ (mappingCone.fst g).1.v i (i + 1) rfl =
        (mappingCone.fst f).1.v i (i + 1) rfl) := by
  subst g
  simp

/-- The native signed shift leaves the integral coordinate unchanged. -/
@[reassoc]
theorem shiftOneIso_hom_a (K : CochainComplex C ℤ) (n : ℕ) (i : ℤ) :
    (shiftOneIso K n).hom.f i ≫ a (K⟦(1 : ℤ)⟧) n i = a K n (i + 1) := by
  let f := n • 𝟙 K
  have h : f⟦(1 : ℤ)⟧' = n • 𝟙 (K⟦(1 : ℤ)⟧) := by
    exact ((CategoryTheory.shiftFunctor _ (1 : ℤ)).map_nsmul (f := 𝟙 K) (n := n)).trans
      (congrArg (n • ·) ((CategoryTheory.shiftFunctor _ (1 : ℤ)).map_id K))
  change ((shiftTriangleIso K n 1).hom.hom₃).f i ≫ a _ n i = _
  rw [shiftTriangleIso_hom₃ K n 1 h]
  change ((mappingCone.shiftIso f 1).hom.f i ≫ _) ≫
    (mappingCone.snd (n • 𝟙 (K⟦(1 : ℤ)⟧))).v i i (add_zero i) = _
  rw [Category.assoc, (transport_hom_coordinates h i).1]
  simp only [mappingCone.shiftIso, mappingCone.lift_f_snd_v, Cochain.shift_v', a]
  rfl

/-- The native signed shift negates the positive Bockstein coordinate. -/
@[reassoc]
theorem shiftOneIso_hom_b (K : CochainComplex C ℤ) (n : ℕ) (i : ℤ) :
    (shiftOneIso K n).hom.f i ≫ b (K⟦(1 : ℤ)⟧) n i = -(b K n (i + 1)) := by
  let f := n • 𝟙 K
  have h : f⟦(1 : ℤ)⟧' = n • 𝟙 (K⟦(1 : ℤ)⟧) := by
    exact ((CategoryTheory.shiftFunctor _ (1 : ℤ)).map_nsmul (f := 𝟙 K) (n := n)).trans
      (congrArg (n • ·) ((CategoryTheory.shiftFunctor _ (1 : ℤ)).map_id K))
  change ((shiftTriangleIso K n 1).hom.hom₃).f i ≫ b _ n i = _
  rw [shiftTriangleIso_hom₃ K n 1 h]
  change ((mappingCone.shiftIso f 1).hom.f i ≫ _) ≫
    (-(mappingCone.fst (n • 𝟙 (K⟦(1 : ℤ)⟧))).1.v i (i + 1) rfl) = _
  rw [Preadditive.comp_neg, Category.assoc, (transport_hom_coordinates h i).2]
  simp only [mappingCone.shiftIso, mappingCone.lift_f_fst_v, Int.negOnePow_one,
    Units.neg_smul, one_smul]
  change -((-(mappingCone.fst f).shift 1 : Cocycle _ _ 1).1.v i (i + 1) rfl) = _
  simp only [Cocycle.coe_neg, Cochain.neg_v, Cocycle.shift_coe, Cochain.shift_v', b]
  rfl

variable {D : Type*} [Category* D] [Preadditive D] [HasBinaryBiproducts D]
  (F : C ⥤ D) [F.Additive]

local notation "R" => Functor.mapHomologicalComplex F (ComplexShape.up ℤ)

/-- The additive comparison commutes with the actual signed shift of the finite cone. -/
theorem mapIso_shiftOne (K : CochainComplex C ℤ) (n : ℕ) :
    let e := (R).commShiftIso (1 : ℤ)
    (R).map (shiftOneIso K n).hom ≫ (mapIso F (K⟦(1 : ℤ)⟧) n).hom ≫
        map n (e.hom.app K) =
      e.hom.app (finiteCoefficients K n) ≫ (mapIso F K n).hom⟦(1 : ℤ)⟧' ≫
        (shiftOneIso ((R).obj K) n).hom := by
  intro e
  let L := K⟦(1 : ℤ)⟧
  let M := (R).obj K
  let s := (shiftOneIso K n).hom
  let t := (shiftOneIso M n).hom
  let x := (mapIso F L n).hom
  let y := (mapIso F K n).hom
  let p := e.hom.app K
  apply HomologicalComplex.hom_ext
  intro i
  change F.map (s.f i) ≫ x.f i ≫ (map n p).f i = 𝟙 _ ≫ y.f (i + 1) ≫ t.f i
  apply ext_to (M⟦(1 : ℤ)⟧) n i
  · have h : (map n p).f i ≫ a (M⟦(1 : ℤ)⟧) n i = a ((R).obj L) n i :=
      (map_a n p i).trans (Category.comp_id _)
    have hx : x.f i ≫ a ((R).obj L) n i = F.map (a L n i) := mapIso_hom_a F L n i
    have hy : y.f (i + 1) ≫ a M n (i + 1) = F.map (a K n (i + 1)) :=
      mapIso_hom_a F K n (i + 1)
    have hs : s.f i ≫ a L n i = a K n (i + 1) := shiftOneIso_hom_a K n i
    have ht : t.f i ≫ a (M⟦(1 : ℤ)⟧) n i = a M n (i + 1) := shiftOneIso_hom_a M n i
    simp only [Category.assoc, Category.id_comp, h, hx, ht, hy]
    exact (F.map_comp _ _).symm.trans (F.congr_map hs)
  · have h : (map n p).f i ≫ b (M⟦(1 : ℤ)⟧) n i = b ((R).obj L) n i :=
      (map_b n p i).trans (Category.comp_id _)
    have hx : x.f i ≫ b ((R).obj L) n i = F.map (b L n i) := mapIso_hom_b F L n i
    have hy : y.f (i + 1) ≫ b M n (i + 1) = F.map (b K n (i + 1)) :=
      mapIso_hom_b F K n (i + 1)
    have hs : s.f i ≫ b L n i = -(b K n (i + 1)) := shiftOneIso_hom_b K n i
    have ht : t.f i ≫ b (M⟦(1 : ℤ)⟧) n i = -(b M n (i + 1)) := shiftOneIso_hom_b M n i
    simp only [Category.assoc, Category.id_comp, h, hx, ht, Preadditive.comp_neg, hy]
    exact (F.map_comp _ _).symm.trans ((F.congr_map hs).trans F.map_neg)

variable {E : Type*} [Category* E] [Preadditive E] [HasBinaryBiproducts E]
  (G : D ⥤ E) [G.Additive]

/-- Applying two additive comparisons to the original cone gives the
comparison for the composite functor on both signed coordinates. -/
theorem mapIso_comp_hom (K : CochainComplex C ℤ) (n : ℕ) :
    (mapIso (F ⋙ G) K n).hom =
      (G.mapHomologicalComplex (.up ℤ)).map (mapIso F K n).hom ≫
        (mapIso G ((R).obj K) n).hom := by
  let L := (R).obj K
  let G' := G.mapHomologicalComplex (.up ℤ)
  let M := G'.obj L
  let x := (mapIso (F ⋙ G) K n).hom
  let y := (mapIso G L n).hom
  let z := (mapIso F K n).hom
  apply HomologicalComplex.hom_ext
  intro i
  change x.f i = G.map (z.f i) ≫ y.f i
  apply ext_to M n i
  · have hx : x.f i ≫ a M n i = G.map (F.map (a K n i)) :=
      mapIso_hom_a (F ⋙ G) K n i
    have hy : y.f i ≫ a M n i = G.map (a L n i) := mapIso_hom_a G L n i
    have hz : z.f i ≫ a L n i = F.map (a K n i) := mapIso_hom_a F K n i
    rw [hx, Category.assoc, hy, ← G.map_comp, hz]
  · have hx : x.f i ≫ b M n i = G.map (F.map (b K n i)) :=
      mapIso_hom_b (F ⋙ G) K n i
    have hy : y.f i ≫ b M n i = G.map (b L n i) := mapIso_hom_b G L n i
    have hz : z.f i ≫ b L n i = F.map (b K n i) := mapIso_hom_b F K n i
    rw [hx, Category.assoc, hy, ← G.map_comp, hz]

end CochainComplex.finiteCoefficients
