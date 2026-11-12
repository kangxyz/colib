/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Morphisms.UniversallyInjective.ResidueDegree
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.RadicialTransfer
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.GraphRestriction
public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Actual radicial pullback isomorphisms on torsion presheaves with transfers

The inverse to the original graph pullback is the constructed transposed-graph transfer
multiplied by the explicit integer Bezout coefficient Nat.gcdA(d,n), where d is the full
generic residue degree. Both inverse equations use the proved native degree composites.
Only n-torsion on the two original section groups is required, not homotopy invariance.
If n is invertible in the original base field, the actual radicial degree theorem supplies
coprimality. This is an objectwise result, not a field-change or perfection equivalence.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k] (P : PresheafWithTransfers.{v} k)
  {X Y : Scheme.SmoothSite (Spec (.of k))} (q : X ⟶ Y)
  [IsIntegral X.left] [IsIntegral Y.left] [IsFinite q.left] [Flat q.left]
  [UniversallyInjective q.left]

/-- The original graph pullback, with its explicit Bezout-scaled genuine transfer inverse.
The coprimality premise concerns the full generic residue degree. -/
@[colib_tag "COL-1094", colib_ref "MVW2006"
  "Lecture 1, Exercise 1.11, printed p. 6; Lecture 2, Definition 2.1, printed p. 13"
  "adaptation" "explicit Bezout inverse to the original graph pullback on torsion sections"]
def radicialGraphIsoOfCoprime (n : ℕ)
    (hX : Module.IsTorsionBy ℤ (sections P (Cor.mk X)) (n : ℤ))
    (hY : Module.IsTorsionBy ℤ (sections P (Cor.mk Y)) (n : ℤ))
    (hcop : (q.left.residueDegree (genericPoint X.left)).Coprime n) :
    sections P (Cor.mk Y) ≅ sections P (Cor.mk X) := by
  let d := q.left.residueDegree (genericPoint X.left)
  let a : ℤ := Nat.gcdA d n
  have hscalar (A : AddCommGrpCat.{v}) (hA : Module.IsTorsionBy ℤ A (n : ℤ)) :
      a • ((d : ℤ) • 𝟙 A) = 𝟙 A := by
    ext x
    change a • ((d : ℤ) • x) = x
    have hab : (d : ℤ) * Nat.gcdA d n + (n : ℤ) * Nat.gcdB d n = 1 := by
      rw [← Nat.gcd_eq_gcd_ab, hcop.gcd_eq_one]
      rfl
    have hc := congrArg (fun z : ℤ => z • x) hab
    rw [add_smul, mul_smul, mul_smul, hA, add_zero, one_smul] at hc
    exact (smul_comm a (d : ℤ) x).trans hc
  let g : sections P (Cor.mk Y) ⟶ sections P (Cor.mk X) :=
    transfer P ((Cor.graphFunctor k).map q)
  let t : sections P (Cor.mk X) ⟶ sections P (Cor.mk Y) :=
    transfer P (Cor.finiteFlatTranspose k q)
  have hgt : g ≫ t = (d : ℤ) • 𝟙 (sections P (Cor.mk Y)) :=
    transfer_graph_comp_finiteFlatTranspose P q
  have htg : t ≫ g = (d : ℤ) • 𝟙 (sections P (Cor.mk X)) :=
    transfer_finiteFlatTranspose_comp_graph P q
  exact
    { hom := g
      inv := a • t
      hom_inv_id := by rw [Preadditive.comp_zsmul, hgt]; exact hscalar _ hY
      inv_hom_id := by rw [Preadditive.zsmul_comp, htg]; exact hscalar _ hX }

@[simp]
theorem radicialGraphIsoOfCoprime_hom (n : ℕ)
    (hX : Module.IsTorsionBy ℤ (sections P (Cor.mk X)) (n : ℤ))
    (hY : Module.IsTorsionBy ℤ (sections P (Cor.mk Y)) (n : ℤ))
    (hcop : (q.left.residueDegree (genericPoint X.left)).Coprime n) :
    (radicialGraphIsoOfCoprime P q n hX hY hcop).hom =
      ((toPresheaf k).obj P).map q.op := rfl

@[simp]
theorem radicialGraphIsoOfCoprime_inv (n : ℕ)
    (hX : Module.IsTorsionBy ℤ (sections P (Cor.mk X)) (n : ℤ))
    (hY : Module.IsTorsionBy ℤ (sections P (Cor.mk Y)) (n : ℤ))
    (hcop : (q.left.residueDegree (genericPoint X.left)).Coprime n) :
    (radicialGraphIsoOfCoprime P q n hX hY hcop).inv =
      Nat.gcdA (q.left.residueDegree (genericPoint X.left)) n •
        transfer P (Cor.finiteFlatTranspose k q) := rfl

/-- Prime-to-characteristic torsion sections are invariant under the original finite flat
radicial map, with an explicit inverse and no homotopy-invariance hypothesis. -/
@[colib_tag "COL-1094"]
def radicialGraphIso (n : ℕ) (hn : IsUnit (n : k))
    (hX : Module.IsTorsionBy ℤ (sections P (Cor.mk X)) (n : ℤ))
    (hY : Module.IsTorsionBy ℤ (sections P (Cor.mk Y)) (n : ℤ)) :
    sections P (Cor.mk Y) ≅ sections P (Cor.mk X) :=
  radicialGraphIsoOfCoprime P q n hX hY
    (q.left.residueDegree_coprime_of_isUnit Y.hom (genericPoint X.left) n hn)

/-- The map in the underlying original ordinary presheaf is the hom of this isomorphism. -/
@[simp]
theorem radicialGraphIso_hom (n : ℕ) (hn : IsUnit (n : k))
    (hX : Module.IsTorsionBy ℤ (sections P (Cor.mk X)) (n : ℤ))
    (hY : Module.IsTorsionBy ℤ (sections P (Cor.mk Y)) (n : ℤ)) :
    (radicialGraphIso P q n hn hX hY).hom = ((toPresheaf k).obj P).map q.op := rfl

/-- The inverse remains the explicit integer Bezout multiple of the original transfer. -/
@[simp]
theorem radicialGraphIso_inv (n : ℕ) (hn : IsUnit (n : k))
    (hX : Module.IsTorsionBy ℤ (sections P (Cor.mk X)) (n : ℤ))
    (hY : Module.IsTorsionBy ℤ (sections P (Cor.mk Y)) (n : ℤ)) :
    (radicialGraphIso P q n hn hX hY).inv =
      Nat.gcdA (q.left.residueDegree (genericPoint X.left)) n •
        transfer P (Cor.finiteFlatTranspose k q) := rfl

/-- The original ordinary presheaf restriction along the radicial map is an isomorphism. -/
@[colib_tag "COL-1094"]
theorem isIso_toPresheaf_map_of_radicial (n : ℕ) (hn : IsUnit (n : k))
    (hX : Module.IsTorsionBy ℤ (sections P (Cor.mk X)) (n : ℤ))
    (hY : Module.IsTorsionBy ℤ (sections P (Cor.mk Y)) (n : ℤ)) :
    IsIso (((toPresheaf k).obj P).map q.op) :=
  (radicialGraphIso P q n hn hX hY).isIso_hom

end AlgebraicGeometry.PresheafWithTransfers
