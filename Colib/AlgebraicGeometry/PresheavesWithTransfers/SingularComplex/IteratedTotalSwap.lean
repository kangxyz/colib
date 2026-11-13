/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.IteratedTotalComparison
import Colib.Algebra.Homology.CochainComplex.TotalColumnComparison

/-!
# Symmetry of iterated singular totalization

The double singular bicomplex exchanges its two actual simplex factors.
Its total symmetry carries the Koszul sign of the two simplex degrees.
Finite diagonal support compares this construction with iterating the
original singular total functor on a bounded-above coefficient complex.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open HomologicalComplex HomologicalComplex₂
open scoped Simplicial

universe u v

namespace AlgebraicGeometry.PresheafWithTransfers

open _root_.AlgebraicGeometry.Scheme SmoothSite

variable {k : Type u} [Field k]

local notation "c" => ComplexShape.up ℤ
local notation "S" => singularCoChains k

private abbrev doubleSingularColumnSwap (P : PresheafWithTransfers.{v} k) :
    (doubleSingularCochainBicomplex P).total c ≅
      (doubleSingularCochainBicomplex P).total c :=
  HomologicalComplex₂.total.mapIso (doubleSingularCochainBicomplexSwap P) c ≪≫
    (doubleSingularCochainBicomplex P).totalFlipIso c

private theorem doubleSingularColumnSwap_natural {P Q : PresheafWithTransfers.{v} k} (f : P ⟶ Q) :
    (doubleSingularColumnSwap P).hom ≫
        HomologicalComplex₂.total.map ((doubleSingularCochainBicomplexFunctor k).map f) c =
      HomologicalComplex₂.total.map ((doubleSingularCochainBicomplexFunctor k).map f) c ≫
        (doubleSingularColumnSwap Q).hom := by
  let B := doubleSingularCochainBicomplex P
  let D := doubleSingularCochainBicomplex Q
  let a : B ⟶ D := (doubleSingularCochainBicomplexFunctor k).map f
  let b := (doubleSingularCochainBicomplexSwap P).hom
  let d := (doubleSingularCochainBicomplexSwap Q).hom
  change (HomologicalComplex₂.total.map b c ≫ (B.totalFlipIso c).hom) ≫
    HomologicalComplex₂.total.map a c =
    HomologicalComplex₂.total.map a c ≫
      HomologicalComplex₂.total.map d c ≫ (D.totalFlipIso c).hom
  rw [Category.assoc, ← HomologicalComplex₂.totalFlipIso_hom_naturality_map a,
    ← Category.assoc, ← HomologicalComplex₂.total.map_comp,
    doubleSingularCochainBicomplexSwap_natural f, HomologicalComplex₂.total.map_comp,
    Category.assoc]

private def iteratedSingularColumnSwap (K : CochainComplex (PresheafWithTransfers.{v} k) ℤ) :
    (iteratedSingularTricomplex K).int₂₃ c ≅ (iteratedSingularTricomplex K).int₂₃ c :=
  HomologicalComplex.Hom.isoOfComponents (fun p => doubleSingularColumnSwap (K.X p))
    (fun p q _ => doubleSingularColumnSwap_natural (K.d p q))

/-- Swapping the two original simplices on the iterated singular total complex. -/
@[no_expose]
def iteratedSingularTotalSwap
    (K : CochainComplex (PresheafWithTransfers.{v} k) ℤ) (b : ℤ) [K.IsStrictlyLE b] :
    (singularTotalFunctor k).obj ((singularTotalFunctor k).obj K) ≅
      (singularTotalFunctor k).obj ((singularTotalFunctor k).obj K) :=
  (iteratedSingularTotalFromColumns K b).symm ≪≫
    HomologicalComplex₂.total.mapIso (iteratedSingularColumnSwap K) c ≪≫
    iteratedSingularTotalFromColumns K b

private theorem doubleSingularColumnSwap_summand
    (P : PresheafWithTransfers.{v} k) (q r n : ℤ) (h : q + r = n) :
    (doubleSingularCochainBicomplex P).ιTotal c q r n h ≫ (doubleSingularColumnSwap P).hom.f n =
      (q * r).negOnePow • ((doubleSingularCochainTermSwap P q r).hom ≫
        (doubleSingularCochainBicomplex P).ιTotal c r q n (by
          change r + q = n
          omega)) := by
  let B := doubleSingularCochainBicomplex P
  let e := (doubleSingularCochainBicomplexSwap P).hom
  change B.ιTotal c q r n h ≫
      ((HomologicalComplex₂.total.map e c).f n ≫ (B.totalFlipIso c).hom.f n) = _
  rw [ιTotal_map_assoc, ιTotal_totalFlipIso_f_hom, Linear.comp_units_smul,
    doubleSingularCochainBicomplexSwap_hom_f_f]
  change (r * q).negOnePow • _ = (q * r).negOnePow • _
  rw [mul_comm r q]

private theorem iteratedSingularColumnSwap_summand
    (K : CochainComplex (PresheafWithTransfers.{v} k) ℤ) (p q r n : ℤ) (h : p + (q + r) = n) :
    (iteratedSingularTricomplex K).ιTotal₂₃ c c p q r n h ≫
        (HomologicalComplex₂.total.map (iteratedSingularColumnSwap K).hom c).f n =
      (q * r).negOnePow • ((doubleSingularCochainTermSwap (K.X p) q r).hom ≫
        (iteratedSingularTricomplex K).ιTotal₂₃ c c p r q n (by
          change p + (r + q) = n
          omega)) := by
  let T := iteratedSingularTricomplex K
  let e := (iteratedSingularColumnSwap K).hom
  let B := doubleSingularCochainBicomplex (K.X p)
  let a := doubleSingularColumnSwap (K.X p)
  let m := q + r
  let ι := (T.int₂₃ c).ιTotal c p m n h
  let σ := (q * r).negOnePow
  let τ := (doubleSingularCochainTermSwap (K.X p) q r).hom
  have h' : r + q = m := add_comm r q
  have h₀ : p + (r + q) = n := by omega
  have he : ι ≫ (HomologicalComplex₂.total.map e c).f n = a.hom.f m ≫ ι :=
    ιTotal_map (T.int₂₃ c) (T.int₂₃ c) e c p m n h
  have hs : B.ιTotal c q r m rfl ≫ a.hom.f m = σ • (τ ≫ B.ιTotal c r q m h') :=
    doubleSingularColumnSwap_summand (K.X p) q r m rfl
  have ht : T.ιTotal₂₃ c c p r q n h₀ = B.ιTotal c r q m h' ≫ ι :=
    T.ιTotal₂₃_eq c c p r q n h₀ m h'
  change ((T.X p).ιTotal c q r (q + r) rfl ≫ (T.int₂₃ c).ιTotal c p (q + r) n h) ≫
      (HomologicalComplex₂.total.map e c).f n = σ • (τ ≫ T.ιTotal₂₃ c c p r q n h₀)
  calc
    _ = B.ιTotal c q r m rfl ≫ (a.hom.f m ≫ ι) := by
      exact (Category.assoc _ _ _).trans (congrArg (B.ιTotal c q r m rfl ≫ ·) he)
    _ = (B.ιTotal c q r m rfl ≫ a.hom.f m) ≫ ι := (Category.assoc _ _ _).symm
    _ = (σ • (τ ≫ B.ιTotal c r q m h')) ≫ ι := congrArg (· ≫ ι) hs
    _ = _ := by rw [Linear.units_smul_comp, Category.assoc, ← ht]

/-- The actual two placements of the singular unit are exchanged by the total symmetry. -/
theorem singularTotal_map_unit_comp_iteratedSingularTotalSwap
    (K : CochainComplex (PresheafWithTransfers.{v} k) ℤ) (b : ℤ) [K.IsStrictlyLE b] :
    (singularTotalFunctor k).map ((singularTotalUnit k).app K) ≫
        (iteratedSingularTotalSwap K b).hom =
      (singularTotalUnit k).app ((singularTotalFunctor k).obj K) := by
  let C := singularTotalFunctor k
  let η := singularTotalUnit k
  let B := (singularBicomplexFunctor k).obj K
  let D := (singularBicomplexFunctor k).obj (C.obj K)
  let T := iteratedSingularTricomplex K
  let e := iteratedSingularTotalFromColumns K b
  let s := HomologicalComplex₂.total.map (iteratedSingularColumnSwap K).hom c
  let a := C.map (η.app K)
  let j := η.app (C.obj K)
  have h (p q n : ℤ) (hn : p + q = n) :
      B.ιTotal c p q n hn ≫ a.f n =
        ((S).map (singularZeroInclusion (K.X p))).f q ≫
          T.ιTotal₂₃ c c p 0 q n (by
            change p + (0 + q) = n
            omega) ≫ e.hom.f n := by
    change B.ιTotal c p q n hn ≫
        (HomologicalComplex₂.total.map ((singularBicomplexFunctor k).map (η.app K)) c).f n = _
    rw [ιTotal_map, iteratedSingularTotalFromColumns_summand K b p 0 q p n (add_zero p) hn]
    change ((S).map ((η.app K).f p)).f q ≫ D.ιTotal c p q n hn = _
    change ((S).map (singularZeroInclusion (K.X p) ≫ B.ιTotal c p 0 p (add_zero p))).f q ≫
      D.ιTotal c p q n hn = _
    rw [Functor.map_comp, HomologicalComplex.comp_f, Category.assoc]
  have h' (p q n : ℤ) (hn : p + q = n) :
      B.ιTotal c p q n hn ≫ j.f n =
        singularZeroInclusion ((B.X p).X q) ≫
          T.ιTotal₂₃ c c p q 0 n (by
            change p + (q + 0) = n
            omega) ≫ e.hom.f n := by
    change B.ιTotal c p q n hn ≫ singularZeroInclusion ((B.total c).X n) ≫
        D.ιTotal c n 0 n (add_zero n) = _
    rw [← Category.assoc, singularZeroInclusion_naturality, Category.assoc,
      iteratedSingularTotalFromColumns_summand K b p q 0 n n hn (add_zero n)]
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f]
  apply HomologicalComplex₂.total.hom_ext
  intro p q hn
  change p + q = n at hn
  change B.ιTotal c p q n hn ≫ a.f n ≫ e.inv.f n ≫ s.f n ≫ e.hom.f n =
    B.ιTotal c p q n hn ≫ j.f n
  rw [← Category.assoc (B.ιTotal c p q n hn) (a.f n), h p q n hn]
  simp only [Category.assoc]
  have he : e.hom.f n ≫ e.inv.f n = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, e.hom_inv_id, HomologicalComplex.id_f]
  rw [← Category.assoc (e.hom.f n), he, Category.id_comp]
  rw [← Category.assoc (T.ιTotal₂₃ c c p 0 q n _), iteratedSingularColumnSwap_summand]
  simp only [zero_mul, Int.negOnePow_zero, one_smul, Category.assoc]
  rw [← Category.assoc (((S).map (singularZeroInclusion (K.X p))).f q),
    doubleSingularCochainTermSwap_unit, h' p q n hn]
  rfl

end AlgebraicGeometry.PresheafWithTransfers
