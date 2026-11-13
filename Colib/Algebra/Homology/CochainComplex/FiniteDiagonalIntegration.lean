/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksCore.Algebra.Homology.HomologicalTricomplex.Associator
public import StacksFrontier.Algebra.Homology.TotalComplexFiniteSupport

/-!
# Finite diagonal integration with cochain-valued coefficients

Apply an additive functor to each term of a bicomplex. When the original
bicomplex has finite support on each diagonal, compare integration of the
first two indices with the functor applied to its totalization.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂

universe u v

namespace HomologicalComplex₂.TotalMap

local notation "c" => ComplexShape.up ℤ

variable {A : Type u} [Category.{v} A] [Preadditive A]
  [∀ B : HomologicalComplex₂ A c c, B.HasTotal c]
  (G : A ⥤ CochainComplex A ℤ) [G.Additive] (B : HomologicalComplex₂ A c c)

private abbrev mappedTotal : HomologicalComplex₂ A c c :=
  (G.mapHomologicalComplex c).obj (B.total c)

private abbrev mappedTricomplex : HomologicalComplex₃ A c c c := mapBicomplex G B

local notation "T" => mappedTricomplex G B
local notation "D" => mappedTotal G B

private abbrev cochainEval (r : ℤ) : A ⥤ A :=
  G ⋙ HomologicalComplex.eval A c r

private def integrationSliceMap (m r : ℤ) : (((T).int₁₂ c).X m).X r ⟶ ((D).X m).X r := by
  let E : A ⥤ A := cochainEval G r
  exact HomologicalComplex₂.TotalMap.totalMapf (c₁₂ := c) E B m

private theorem integrationSliceMap_summand (p q m r : ℤ) (hm : p + q = m) :
    ((T).X' r).ιTotal c p q m hm ≫ integrationSliceMap G B m r =
      (G.map (B.ιTotal c p q m hm)).f r := by
  let E : A ⥤ A := cochainEval G r
  exact HomologicalComplex₂.TotalMap.ι_totalMapf (c₁₂ := c) E B m p q hm

private theorem isIso_integrationSliceMap
    (hfin : ∀ n : ℤ, {pq : ℤ × ℤ | pq.1 + pq.2 = n ∧
      ¬ IsZero ((B.X pq.1).X pq.2)}.Finite) (m r : ℤ) : IsIso (integrationSliceMap G B m r) := by
  let E : A ⥤ A := cochainEval G r
  exact HomologicalComplex₂.TotalMap.isIso_totalMapf_of_finite (c₁₂ := c) E B m
    (hfin m)

private theorem integrationSliceMap_inner
    (m r s : ℤ) :
    (((T).int₁₂ c).X m).d r s ≫ integrationSliceMap G B m s =
      integrationSliceMap G B m r ≫
        ((D).X m).d r s := by
  let f := HomologicalComplex₂.total.map ((T).d' r s) c
  let a := integrationSliceMap G B m r
  let a' := integrationSliceMap G B m s
  let d := ((D).X m).d r s
  change f.f m ≫ a' = a ≫ d
  apply HomologicalComplex₂.total.hom_ext c
  intro p q h
  have hm : p + q = m := h
  let ι := ((T).X' r).ιTotal c p q m h
  let ι' := ((T).X' s).ιTotal c p q m h
  let g := G.map (B.ιTotal c p q m h)
  let δ := (((T).X p).X q).d r s
  have hf : ι ≫ f.f m = δ ≫ ι' := ιTotal_map ((T).X' r) ((T).X' s) ((T).d' r s) c p q m h
  have hr : ι ≫ a = g.f r := integrationSliceMap_summand G B p q m r hm
  have hs : ι' ≫ a' = g.f s := integrationSliceMap_summand G B p q m s hm
  calc
    ι ≫ (f.f m ≫ a') = (ι ≫ f.f m) ≫ a' := (Category.assoc _ _ _).symm
    _ = δ ≫ (ι' ≫ a') := (congrArg (· ≫ a') hf).trans (Category.assoc _ _ _)
    _ = δ ≫ g.f s := congrArg (δ ≫ ·) hs
    _ = g.f r ≫ d := (g.comm r s).symm
    _ = (ι ≫ a) ≫ d := congrArg (· ≫ d) hr.symm
    _ = ι ≫ (a ≫ d) := Category.assoc _ _ _

private theorem integrationSliceMap_outer
    (m n r : ℤ) :
    (((T).int₁₂ c).d m n).f r ≫ integrationSliceMap G B n r =
      integrationSliceMap G B m r ≫
        ((D).d m n).f r := by
  let E : A ⥤ A := cochainEval G r
  exact HomologicalComplex₂.TotalMap.d_totalMapf (c₁₂ := c) E B m n

variable (hfin : ∀ n : ℤ, {pq : ℤ × ℤ | pq.1 + pq.2 = n ∧
  ¬ IsZero ((B.X pq.1).X pq.2)}.Finite)

private def integrationColumnIso (m : ℤ) : ((T).int₁₂ c).X m ≅ (D).X m :=
  HomologicalComplex.Hom.isoOfComponents
    (fun r => @asIso _ _ _ _ (integrationSliceMap G B m r)
      (isIso_integrationSliceMap G B hfin m r))
    (fun r s _ => (integrationSliceMap_inner G B m r s).symm)

/-- An additive functor to complexes commutes with finite diagonal integration. -/
@[no_expose]
def integrationIsoOfFinite : (HomologicalComplex₃.int₁₂ (mapBicomplex G B) c) ≅
    (G.mapHomologicalComplex c).obj (B.total c) :=
  HomologicalComplex.Hom.isoOfComponents (integrationColumnIso G B hfin)
    (fun m n _ => HomologicalComplex.hom_ext _ _ (fun r =>
      (integrationSliceMap_outer G B m n r).symm))

/-- Integration sends a summand to its original inclusion acted on by the functor. -/
theorem integrationIsoOfFinite_summand (p q m r : ℤ) (hm : p + q = m) :
    (HomologicalComplex₃.X' (mapBicomplex G B) r).ιTotal c p q m hm ≫
        ((integrationIsoOfFinite G B hfin).hom.f m).f r =
      (G.map (B.ιTotal c p q m hm)).f r :=
  integrationSliceMap_summand G B p q m r hm

/-- Reassociate the two original totals and apply the finite diagonal comparison. -/
@[no_expose]
def iteratedTotalIsoOfFinite :
    (HomologicalComplex₃.total₂₃ (mapBicomplex G B) c c) ≅
      HomologicalComplex₂.total ((G.mapHomologicalComplex c).obj (B.total c)) c :=
  ((T).totalAssociator c c c).symm ≪≫ total.mapIso (integrationIsoOfFinite G B hfin) c

/-- The comparison on a summand uses the two original inclusions in order. -/
theorem iteratedTotalIsoOfFinite_summand
    (p q r m n : ℤ) (hm : p + q = m) (hn : m + r = n) :
    HomologicalComplex₃.ιTotal₂₃ (mapBicomplex G B) c c p q r n (by
        change p + (q + r) = n
        omega) ≫
        (iteratedTotalIsoOfFinite G B hfin).hom.f n =
      (G.map (B.ιTotal c p q m hm)).f r ≫
        HomologicalComplex₂.ιTotal ((G.mapHomologicalComplex c).obj (B.total c)) c m r n hn := by
  let e : (T).total₁₂ c c ≅ (T).total₂₃ c c := (T).totalAssociator c c c
  let d := integrationIsoOfFinite G B hfin
  let d' := total.map d.hom c
  let A' := D
  have h₁ : p + q + r = n := by omega
  have h₂ : p + (q + r) = n := by omega
  have he : (T).ιTotal₁₂ c c p q r n h₁ ≫ e.hom.f n = (T).ιTotal₂₃ c c p q r n h₂ := by
    rw [← (T).ιTotal₁₂OrZero_eq c c p q r n h₁, ← (T).ιTotal₂₃OrZero_eq c c p q r n h₂]
    exact (T).ιTotal₁₂OrZero_totalAssociatorX_hom c c c p q r n
  have hi : e.hom.f n ≫ e.inv.f n = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, e.hom_inv_id, HomologicalComplex.id_f]
  have hs : (T).ιTotal₁₂ c c p q r n h₁ =
      ((T).X' r).ιTotal c p q m hm ≫ ((T).int₁₂ c).ιTotal c m r n hn :=
    (T).ιTotal₁₂_eq c c p q r n h₁ m hm
  have hd : ((T).int₁₂ c).ιTotal c m r n hn ≫ d'.f n =
      (d.hom.f m).f r ≫ A'.ιTotal c m r n hn := ιTotal_map ((T).int₁₂ c) A' d.hom c m r n hn
  unfold iteratedTotalIsoOfFinite
  change (T).ιTotal₂₃ c c p q r n h₂ ≫ (e.inv.f n ≫ d'.f n) = _
  calc
    _ = (T).ιTotal₁₂ c c p q r n h₁ ≫ ((e.hom.f n ≫ e.inv.f n) ≫ d'.f n) := by
      rw [← he]
      simp only [Category.assoc]
    _ = (T).ιTotal₁₂ c c p q r n h₁ ≫ d'.f n := by rw [hi, Category.id_comp]
    _ = (((T).X' r).ιTotal c p q m hm ≫ ((d.hom.f m).f r)) ≫ A'.ιTotal c m r n hn := by
      rw [hs, Category.assoc, hd, ← Category.assoc]
    _ = _ := by rw [integrationIsoOfFinite_summand G B hfin p q m r hm]

end HomologicalComplex₂.TotalMap
