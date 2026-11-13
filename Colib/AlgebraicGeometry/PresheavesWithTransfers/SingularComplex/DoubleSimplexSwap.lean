/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.ParameterNaturality
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.Total
public import Mathlib.Algebra.Category.Grp.Abelian

/-!
# The exchange of two simplex factors in singular complexes

The graphs of the actual simplex factor permutations commute with both
singular differentials. The same permutation exchanges the two placements
of the degree-zero section in the double complex.
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
local notation "d" => ComplexShape.down ℕ
/-- The original singular cochain functor with its coefficient universe fixed. -/
abbrev singularCoChains (k : Type u) [Field k] :
    PresheafWithTransfers.{v} k ⥤ CochainComplex (PresheafWithTransfers.{v} k) ℤ :=
  singularCochainFunctor 0

/-- The original singular chain functor with its coefficient universe fixed. -/
abbrev singularChains (k : Type u) [Field k] :
    PresheafWithTransfers.{v} k ⥤ ChainComplex (PresheafWithTransfers.{v} k) ℕ :=
  singularComplexFunctor

local notation "S" => singularCoChains k
local notation "S₀" => singularChains k
local notation "Δ(" n ")" => AlgebraicSimplex.smoothSiteObj k n

/-- The two simplex degrees before placing them into cochain degrees. -/
abbrev doubleSingularChainBicomplex (P : PresheafWithTransfers.{v} k) :
    HomologicalComplex₂ (PresheafWithTransfers.{v} k) d d :=
  let F : PresheafWithTransfers.{v} k ⥤ ChainComplex (PresheafWithTransfers.{v} k) ℕ :=
    singularChains k
  (F.mapHomologicalComplex d).obj (singularComplex P)

private def doubleSingularChainTermSwap (P : PresheafWithTransfers.{v} k) (q r : ℕ) :
    (((doubleSingularChainBicomplex P).X q).X r) ≅
      (((doubleSingularChainBicomplex P).X r).X q) :=
  ObjectProperty.isoMk _ (Functor.isoWhiskerRight
    (NatIso.op (Cor.parameterProductSwapNatIso (Δ(q)) (Δ(r)))) P.obj)

private theorem doubleSingularChainTermSwap_face
    (P : PresheafWithTransfers.{v} k) (q r : ℕ) (i : Fin (r + 2)) :
    (doubleSingularChainTermSwap P q (r + 1)).hom ≫
        (singularComplexMap (singularFace P r i)).f q =
      singularFace (singularTerm P q) r i ≫ (doubleSingularChainTermSwap P q r).hom := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext X
  let U := X.unop
  let T := Δ(q)
  let V := Δ(r)
  let W := Δ(r + 1)
  let a : V ⟶ W := (AlgebraicSimplex.cosimplicialSmoothSite k).δ i
  let e := (Cor.parameterProductSwapNatIso T V).hom.app U
  let e' := (Cor.parameterProductSwapNatIso T W).hom.app U
  let f := (Cor.parameterProduct T).map ((Cor.parameterProductMap a).app U)
  let g := (Cor.parameterProductMap a).app ((Cor.parameterProduct T).obj U)
  change transfer P e' ≫ transfer P g = transfer P f ≫ transfer P e
  have h : g ≫ e' = e ≫ f := Cor.parameterProductSwapNatIso_secondParameterMap T V a U
  exact (transfer_comp P g e').symm.trans
    ((congrArg (transfer P) h).trans (transfer_comp P e f))

private theorem doubleSingularChainTermSwap_d
    (P : PresheafWithTransfers.{v} k) (q r : ℕ) :
    (doubleSingularChainTermSwap P q (r + 1)).hom ≫
        (singularComplexMap ((singularComplex P).d (r + 1) r)).f q =
      (singularComplex (singularTerm P q)).d (r + 1) r ≫
        (doubleSingularChainTermSwap P q r).hom := by
  rw [singularComplex_d P r, singularComplex_d (singularTerm P q) r]
  change (doubleSingularChainTermSwap P q (r + 1)).hom ≫
      ((S₀).map (∑ i : Fin (r + 2), (-1 : ℤ) ^ (i : ℕ) • singularFace P r i)).f q = _
  let E := (S₀) ⋙ HomologicalComplex.eval (PresheafWithTransfers.{v} k) d q
  change (doubleSingularChainTermSwap P q (r + 1)).hom ≫
      E.map (∑ i : Fin (r + 2), (-1 : ℤ) ^ (i : ℕ) • singularFace P r i) = _
  rw [Functor.map_sum, Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Functor.map_zsmul, Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  exact congrArg ((-1 : ℤ) ^ (i : ℕ) • ·) (doubleSingularChainTermSwap_face P q r i)

private theorem doubleSingularChainTermSwap_d_other
    (P : PresheafWithTransfers.{v} k) (q r : ℕ) :
    (doubleSingularChainTermSwap P (q + 1) r).hom ≫
        (singularComplex (singularTerm P r)).d (q + 1) q =
      (singularComplexMap ((singularComplex P).d (q + 1) q)).f r ≫
        (doubleSingularChainTermSwap P q r).hom := by
  change (withParameterSingularTermIso P (Δ(r)) (q + 1)).hom ≫
      (singularComplex (withParameter P (Δ(r)))).d (q + 1) q =
    ((withParameterFunctor (Δ(r))).map ((singularComplex P).d (q + 1) q)) ≫
      (withParameterSingularTermIso P (Δ(r)) q).hom
  exact (withParameterSingularComplexIso P (Δ(r))).hom.comm (q + 1) q

private theorem doubleSingularChainTermSwap_natural
    {P Q : PresheafWithTransfers.{v} k} (a : P ⟶ Q) (q r : ℕ) :
    (doubleSingularChainTermSwap P q r).hom ≫
        (singularComplexMap ((singularComplexMap a).f r)).f q =
      (singularComplexMap ((singularComplexMap a).f q)).f r ≫
        (doubleSingularChainTermSwap Q q r).hom := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext X
  let e := (Cor.parameterProductSwapNatIso (Δ(q)) (Δ(r))).hom.app X.unop
  change transfer P e ≫ a.hom.app _ = a.hom.app _ ≫ transfer Q e
  exact a.hom.naturality e.op

/-- The double chain bicomplex exchanges the actual simplex factors. -/
@[no_expose]
def doubleSingularChainBicomplexSwap (P : PresheafWithTransfers.{v} k) :
    doubleSingularChainBicomplex P ≅ (doubleSingularChainBicomplex P).flip :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => HomologicalComplex.Hom.isoOfComponents (doubleSingularChainTermSwap P q) (by
      intro r s h
      have hr : s + 1 = r := h
      subst r
      exact doubleSingularChainTermSwap_d P q s))
    (by
      intro q s h
      have hq : s + 1 = q := h
      subst q
      apply HomologicalComplex.hom_ext
      intro r
      exact doubleSingularChainTermSwap_d_other P s r)

/-- The two original simplex degrees placed in nonpositive cochain degrees. -/
abbrev doubleSingularCochainBicomplex (P : PresheafWithTransfers.{v} k) :
    HomologicalComplex₂ (PresheafWithTransfers.{v} k) c c :=
  let F : PresheafWithTransfers.{v} k ⥤ CochainComplex (PresheafWithTransfers.{v} k) ℤ :=
    singularCoChains k
  (F.mapHomologicalComplex c).obj (singularCochainComplex P 0)

private def singularDegreeIso (P : PresheafWithTransfers.{v} k) (i : ℤ) (r : ℕ)
    (h : (ComplexShape.embeddingUpIntLE 0).f r = i) :
    (singularCochainComplex P 0).X i ≅ singularTerm P r :=
  (singularComplex P).extendXIso (ComplexShape.embeddingUpIntLE 0) h

private theorem singularDegreeIso_d (P : PresheafWithTransfers.{v} k) (i j : ℤ) (r s : ℕ)
    (hi : (ComplexShape.embeddingUpIntLE 0).f r = i)
    (hj : (ComplexShape.embeddingUpIntLE 0).f s = j) :
    (singularCochainComplex P 0).d i j ≫ (singularDegreeIso P j s hj).hom =
      (singularDegreeIso P i r hi).hom ≫ (singularComplex P).d r s := by
  rw [show (singularCochainComplex P 0).d i j =
      (singularDegreeIso P i r hi).hom ≫ (singularComplex P).d r s ≫
        (singularDegreeIso P j s hj).inv from
      (singularComplex P).extend_d_eq (ComplexShape.embeddingUpIntLE 0) hi hj]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem singularDegreeIso_map
    {P Q : PresheafWithTransfers.{v} k} (a : P ⟶ Q) (i : ℤ) (r : ℕ)
    (h : (ComplexShape.embeddingUpIntLE 0).f r = i) :
    ((S).map a).f i ≫ (singularDegreeIso Q i r h).hom =
      (singularDegreeIso P i r h).hom ≫ (singularComplexMap a).f r := by
  rw [show ((S).map a).f i =
      (singularDegreeIso P i r h).hom ≫ (singularComplexMap a).f r ≫
        (singularDegreeIso Q i r h).inv from
      extendMap_f (singularComplexMap a) (ComplexShape.embeddingUpIntLE 0) h]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem exists_singularDegree {i : ℤ} (h : i ≤ 0) :
    ∃ r : ℕ, (ComplexShape.embeddingUpIntLE 0).f r = i := by
  refine ⟨(-i).toNat, ?_⟩
  change 0 - (↑(-i).toNat : ℤ) = i
  omega

private def doubleSingularPlacedTermIso (P : PresheafWithTransfers.{v} k) (q r : ℤ) (a b : ℕ)
    (ha : (ComplexShape.embeddingUpIntLE 0).f a = q)
    (hb : (ComplexShape.embeddingUpIntLE 0).f b = r) :
    (((doubleSingularCochainBicomplex P).X q).X r) ≅
      (((doubleSingularChainBicomplex P).X a).X b) :=
  singularDegreeIso ((singularCochainComplex P 0).X q) r b hb ≪≫
    ((S₀) ⋙ HomologicalComplex.eval (PresheafWithTransfers.{v} k) d b).mapIso
      (singularDegreeIso P q a ha)

private theorem doubleSingularPlacedTermIso_inner
    (P : PresheafWithTransfers.{v} k) (q r s : ℤ) (a b b' : ℕ)
    (ha : (ComplexShape.embeddingUpIntLE 0).f a = q)
    (hb : (ComplexShape.embeddingUpIntLE 0).f b = r)
    (hb' : (ComplexShape.embeddingUpIntLE 0).f b' = s) :
    ((doubleSingularCochainBicomplex P).X q).d r s ≫
        (doubleSingularPlacedTermIso P q s a b' ha hb').hom =
      (doubleSingularPlacedTermIso P q r a b ha hb).hom ≫
        ((doubleSingularChainBicomplex P).X a).d b b' := by
  let Pq := (singularCochainComplex P 0).X q
  let f := singularDegreeIso P q a ha
  change (singularCochainComplex Pq 0).d r s ≫
      (singularDegreeIso Pq s b' hb').hom ≫ (singularComplexMap f.hom).f b' =
    ((singularDegreeIso Pq r b hb).hom ≫ (singularComplexMap f.hom).f b) ≫
      (singularComplex (singularTerm P a)).d b b'
  rw [← Category.assoc, singularDegreeIso_d Pq r s b b' hb hb', Category.assoc,
    ← (singularComplexMap f.hom).comm, ← Category.assoc]

private theorem doubleSingularPlacedTermIso_outer
    (P : PresheafWithTransfers.{v} k) (q q' r : ℤ) (a a' b : ℕ)
    (ha : (ComplexShape.embeddingUpIntLE 0).f a = q)
    (ha' : (ComplexShape.embeddingUpIntLE 0).f a' = q')
    (hb : (ComplexShape.embeddingUpIntLE 0).f b = r) :
    ((doubleSingularCochainBicomplex P).d q q').f r ≫
        (doubleSingularPlacedTermIso P q' r a' b ha' hb).hom =
      (doubleSingularPlacedTermIso P q r a b ha hb).hom ≫
        ((doubleSingularChainBicomplex P).d a a').f b := by
  let K := singularCochainComplex P 0
  let E := (S₀) ⋙ HomologicalComplex.eval (PresheafWithTransfers.{v} k) d b
  let f := singularDegreeIso P q a ha
  let g := singularDegreeIso P q' a' ha'
  let i := singularDegreeIso (K.X q) r b hb
  let j := singularDegreeIso (K.X q') r b hb
  have h : E.map (K.d q q') ≫ E.map g.hom =
      E.map f.hom ≫ E.map ((singularComplex P).d a a') := by
    rw [← E.map_comp, ← E.map_comp, singularDegreeIso_d P q q' a a' ha ha']
  change ((S).map (K.d q q')).f r ≫ j.hom ≫ E.map g.hom =
    (i.hom ≫ E.map f.hom) ≫ E.map ((singularComplex P).d a a')
  rw [← Category.assoc, singularDegreeIso_map (K.d q q') r b hb]
  change (i.hom ≫ E.map (K.d q q')) ≫ E.map g.hom =
    (i.hom ≫ E.map f.hom) ≫ E.map ((singularComplex P).d a a')
  rw [Category.assoc, h, ← Category.assoc]

private theorem doubleSingularPlacedTermIso_natural
    {P Q : PresheafWithTransfers.{v} k} (f : P ⟶ Q) (q r : ℤ) (a b : ℕ)
    (ha : (ComplexShape.embeddingUpIntLE 0).f a = q)
    (hb : (ComplexShape.embeddingUpIntLE 0).f b = r) :
    ((S).map (((S).map f).f q)).f r ≫
        (doubleSingularPlacedTermIso Q q r a b ha hb).hom =
      (doubleSingularPlacedTermIso P q r a b ha hb).hom ≫
        (singularComplexMap ((singularComplexMap f).f a)).f b := by
  let E := (S₀) ⋙ HomologicalComplex.eval (PresheafWithTransfers.{v} k) d b
  let i := singularDegreeIso ((singularCochainComplex P 0).X q) r b hb
  let j := singularDegreeIso ((singularCochainComplex Q 0).X q) r b hb
  let eP := singularDegreeIso P q a ha
  let eQ := singularDegreeIso Q q a ha
  have h : E.map (((S).map f).f q) ≫ E.map eQ.hom =
      E.map eP.hom ≫ E.map ((singularComplexMap f).f a) := by
    rw [← E.map_comp, ← E.map_comp, singularDegreeIso_map f q a ha]
  change ((S).map (((S).map f).f q)).f r ≫ j.hom ≫ E.map eQ.hom =
    (i.hom ≫ E.map eP.hom) ≫ E.map ((singularComplexMap f).f a)
  rw [← Category.assoc, singularDegreeIso_map (((S).map f).f q) r b hb]
  change (i.hom ≫ E.map (((S).map f).f q)) ≫ E.map eQ.hom =
    (i.hom ≫ E.map eP.hom) ≫ E.map ((singularComplexMap f).f a)
  rw [Category.assoc, h, ← Category.assoc]

private theorem isZero_doubleSingularCochainTerm (P : PresheafWithTransfers.{v} k) (q r : ℤ)
    (h : 0 < q ∨ 0 < r) : IsZero (((doubleSingularCochainBicomplex P).X q).X r) := by
  rcases h with hq | hr
  · let E := (S) ⋙ HomologicalComplex.eval (PresheafWithTransfers.{v} k) c r
    exact E.map_isZero (isZero_singularCochainComplex_X P 0 q hq)
  · exact isZero_singularCochainComplex_X ((singularCochainComplex P 0).X q) 0 r hr

private theorem singularDegree_eq_sub_natCast (a : ℕ) :
    (ComplexShape.embeddingUpIntLE 0).f a = 0 - (a : ℤ) := rfl

/-- The term isomorphism for the actual exchange of the two cochain degrees. -/
@[no_expose]
def doubleSingularCochainTermSwap (P : PresheafWithTransfers.{v} k) (q r : ℤ) :
    (((doubleSingularCochainBicomplex P).X q).X r) ≅
      (((doubleSingularCochainBicomplex P).X r).X q) :=
  if hq : 0 < q then
    (isZero_doubleSingularCochainTerm P q r (Or.inl hq)).iso
      (isZero_doubleSingularCochainTerm P r q (Or.inr hq))
  else if hr : 0 < r then
    (isZero_doubleSingularCochainTerm P q r (Or.inr hr)).iso
      (isZero_doubleSingularCochainTerm P r q (Or.inl hr))
  else
    doubleSingularPlacedTermIso P q r (-q).toNat (-r).toNat (by
      change 0 - (↑(-q).toNat : ℤ) = q
      omega) (by
      change 0 - (↑(-r).toNat : ℤ) = r
      omega) ≪≫ doubleSingularChainTermSwap P (-q).toNat (-r).toNat ≪≫
    (doubleSingularPlacedTermIso P r q (-r).toNat (-q).toNat (by
      change 0 - (↑(-r).toNat : ℤ) = r
      omega) (by
      change 0 - (↑(-q).toNat : ℤ) = q
      omega)).symm

private theorem doubleSingularCochainTermSwap_eq
    (P : PresheafWithTransfers.{v} k) (a b : ℕ) :
    doubleSingularCochainTermSwap P (0 - (a : ℤ)) (0 - (b : ℤ)) =
      doubleSingularPlacedTermIso P (0 - (a : ℤ)) (0 - (b : ℤ)) a b
        (singularDegree_eq_sub_natCast a) (singularDegree_eq_sub_natCast b) ≪≫
      doubleSingularChainTermSwap P a b ≪≫
      (doubleSingularPlacedTermIso P (0 - (b : ℤ)) (0 - (a : ℤ)) b a
        (singularDegree_eq_sub_natCast b) (singularDegree_eq_sub_natCast a)).symm := by
  have ha₀ : ¬ 0 < 0 - (a : ℤ) := by omega
  have hb₀ : ¬ 0 < 0 - (b : ℤ) := by omega
  have ha : (-(0 - (a : ℤ))).toNat = a := by omega
  have hb : (-(0 - (b : ℤ))).toNat = b := by omega
  unfold doubleSingularCochainTermSwap
  rw [dite_eq_right ha₀, dite_eq_right hb₀]
  let e (a' b' : ℕ)
      (ha' : (ComplexShape.embeddingUpIntLE 0).f a' = 0 - (a : ℤ))
      (hb' : (ComplexShape.embeddingUpIntLE 0).f b' = 0 - (b : ℤ)) :=
    doubleSingularPlacedTermIso P (0 - (a : ℤ)) (0 - (b : ℤ)) a' b' ha' hb' ≪≫
      doubleSingularChainTermSwap P a' b' ≪≫
      (doubleSingularPlacedTermIso P (0 - (b : ℤ)) (0 - (a : ℤ)) b' a' hb' ha').symm
  have he (a' b' : ℕ) (ea : a' = a) (eb : b' = b) (ha' hb') :
      e a' b' ha' hb' =
        e a b (singularDegree_eq_sub_natCast a) (singularDegree_eq_sub_natCast b) := by
    subst a'
    subst b'
    rfl
  exact he _ _ ha hb _ _

private theorem doubleSingularCochainTermSwap_inner (P : PresheafWithTransfers.{v} k) (q r s : ℤ) :
    (doubleSingularCochainTermSwap P q r).hom ≫
        ((doubleSingularCochainBicomplex P).d r s).f q =
      ((doubleSingularCochainBicomplex P).X q).d r s ≫
        (doubleSingularCochainTermSwap P q s).hom := by
  by_cases hq : 0 < q
  · exact (isZero_doubleSingularCochainTerm P q r (Or.inl hq)).eq_of_src _ _
  by_cases hr : 0 < r
  · exact (isZero_doubleSingularCochainTerm P q r (Or.inr hr)).eq_of_src _ _
  by_cases hs : 0 < s
  · exact (isZero_doubleSingularCochainTerm P s q (Or.inl hs)).eq_of_tgt _ _
  by_cases hrel : (ComplexShape.up ℤ).Rel r s
  · obtain ⟨a, ha⟩ := exists_singularDegree (show q ≤ 0 by omega)
    obtain ⟨b, hb⟩ := exists_singularDegree (show r ≤ 0 by omega)
    obtain ⟨b', hb'⟩ := exists_singularDegree (show s ≤ 0 by omega)
    change 0 - (a : ℤ) = q at ha
    change 0 - (b : ℤ) = r at hb
    change 0 - (b' : ℤ) = s at hb'
    change r + 1 = s at hrel
    have he : b' + 1 = b := by omega
    subst q
    subst r
    subst s
    subst b
    rw [doubleSingularCochainTermSwap_eq, doubleSingularCochainTermSwap_eq]
    let a₀ := 0 - (a : ℤ)
    let b₀ := 0 - ((b' + 1 : ℕ) : ℤ)
    let b₁ := 0 - (b' : ℤ)
    let e := doubleSingularPlacedTermIso P b₁ a₀ b' a
      (singularDegree_eq_sub_natCast b') (singularDegree_eq_sub_natCast a)
    let e₀ := doubleSingularPlacedTermIso P b₀ a₀ (b' + 1) a
      (singularDegree_eq_sub_natCast (b' + 1)) (singularDegree_eq_sub_natCast a)
    let f := doubleSingularPlacedTermIso P a₀ b₀ a (b' + 1)
      (singularDegree_eq_sub_natCast a) (singularDegree_eq_sub_natCast (b' + 1))
    let f' := doubleSingularPlacedTermIso P a₀ b₁ a b'
      (singularDegree_eq_sub_natCast a) (singularDegree_eq_sub_natCast b')
    let s₀ := (doubleSingularChainTermSwap P a (b' + 1)).hom
    let s₁ := (doubleSingularChainTermSwap P a b').hom
    apply (cancel_mono e.hom).1
    change (f.hom ≫ s₀ ≫ e₀.inv) ≫ ((doubleSingularCochainBicomplex P).d b₀ b₁).f a₀ ≫
        e.hom =
      (((doubleSingularCochainBicomplex P).X a₀).d b₀ b₁ ≫ f'.hom ≫ s₁ ≫ e.inv) ≫ e.hom
    have hl := doubleSingularPlacedTermIso_outer P b₀ b₁ a₀ (b' + 1) b' a
      (singularDegree_eq_sub_natCast (b' + 1)) (singularDegree_eq_sub_natCast b')
      (singularDegree_eq_sub_natCast a)
    have hr := doubleSingularPlacedTermIso_inner P a₀ b₀ b₁ a (b' + 1) b'
      (singularDegree_eq_sub_natCast a) (singularDegree_eq_sub_natCast (b' + 1))
      (singularDegree_eq_sub_natCast b')
    calc
      _ = f.hom ≫ s₀ ≫
          (e₀.inv ≫ (((doubleSingularCochainBicomplex P).d b₀ b₁).f a₀ ≫ e.hom)) := by
        simp only [Category.assoc]
      _ = f.hom ≫ s₀ ≫ ((doubleSingularChainBicomplex P).d (b' + 1) b').f a := by
        rw [hl, Iso.inv_hom_id_assoc]
      _ = f.hom ≫ ((doubleSingularChainBicomplex P).X a).d (b' + 1) b' ≫ s₁ :=
        congrArg (f.hom ≫ ·) (doubleSingularChainTermSwap_d P a b')
      _ = _ := by
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        rw [← Category.assoc f.hom, ← hr, Category.assoc]
  · rw [(doubleSingularCochainBicomplex P).shape r s hrel,
      HomologicalComplex.zero_f, ((doubleSingularCochainBicomplex P).X q).shape r s hrel,
      comp_zero, zero_comp]

private theorem doubleSingularCochainTermSwap_outer (P : PresheafWithTransfers.{v} k) (q s r : ℤ) :
    (doubleSingularCochainTermSwap P q r).hom ≫
        ((doubleSingularCochainBicomplex P).X r).d q s =
      ((doubleSingularCochainBicomplex P).d q s).f r ≫
        (doubleSingularCochainTermSwap P s r).hom := by
  by_cases hq : 0 < q
  · exact (isZero_doubleSingularCochainTerm P q r (Or.inl hq)).eq_of_src _ _
  by_cases hr : 0 < r
  · exact (isZero_doubleSingularCochainTerm P q r (Or.inr hr)).eq_of_src _ _
  by_cases hs : 0 < s
  · exact (isZero_doubleSingularCochainTerm P r s (Or.inr hs)).eq_of_tgt _ _
  by_cases hrel : (ComplexShape.up ℤ).Rel q s
  · obtain ⟨a, ha⟩ := exists_singularDegree (show q ≤ 0 by omega)
    obtain ⟨a', ha'⟩ := exists_singularDegree (show s ≤ 0 by omega)
    obtain ⟨b, hb⟩ := exists_singularDegree (show r ≤ 0 by omega)
    change 0 - (a : ℤ) = q at ha
    change 0 - (a' : ℤ) = s at ha'
    change 0 - (b : ℤ) = r at hb
    change q + 1 = s at hrel
    have he : a' + 1 = a := by omega
    subst q
    subst s
    subst r
    subst a
    rw [doubleSingularCochainTermSwap_eq, doubleSingularCochainTermSwap_eq]
    let a₀ := 0 - ((a' + 1 : ℕ) : ℤ)
    let a₁ := 0 - (a' : ℤ)
    let b₀ := 0 - (b : ℤ)
    let e := doubleSingularPlacedTermIso P b₀ a₁ b a'
      (singularDegree_eq_sub_natCast b) (singularDegree_eq_sub_natCast a')
    let e₀ := doubleSingularPlacedTermIso P b₀ a₀ b (a' + 1)
      (singularDegree_eq_sub_natCast b) (singularDegree_eq_sub_natCast (a' + 1))
    let f := doubleSingularPlacedTermIso P a₀ b₀ (a' + 1) b
      (singularDegree_eq_sub_natCast (a' + 1)) (singularDegree_eq_sub_natCast b)
    let f' := doubleSingularPlacedTermIso P a₁ b₀ a' b
      (singularDegree_eq_sub_natCast a') (singularDegree_eq_sub_natCast b)
    let s₀ := (doubleSingularChainTermSwap P (a' + 1) b).hom
    let s₁ := (doubleSingularChainTermSwap P a' b).hom
    apply (cancel_mono e.hom).1
    change (f.hom ≫ s₀ ≫ e₀.inv) ≫ ((doubleSingularCochainBicomplex P).X b₀).d a₀ a₁ ≫
        e.hom =
      ((((doubleSingularCochainBicomplex P).d a₀ a₁).f b₀) ≫ f'.hom ≫ s₁ ≫ e.inv) ≫ e.hom
    have hl := doubleSingularPlacedTermIso_inner P b₀ a₀ a₁ b (a' + 1) a'
      (singularDegree_eq_sub_natCast b) (singularDegree_eq_sub_natCast (a' + 1))
      (singularDegree_eq_sub_natCast a')
    have hr := doubleSingularPlacedTermIso_outer P a₀ a₁ b₀ (a' + 1) a' b
      (singularDegree_eq_sub_natCast (a' + 1)) (singularDegree_eq_sub_natCast a')
      (singularDegree_eq_sub_natCast b)
    calc
      _ = f.hom ≫ s₀ ≫
          (e₀.inv ≫ (((doubleSingularCochainBicomplex P).X b₀).d a₀ a₁ ≫ e.hom)) := by
        simp only [Category.assoc]
      _ = f.hom ≫ s₀ ≫ ((doubleSingularChainBicomplex P).X b).d (a' + 1) a' := by
        rw [hl, Iso.inv_hom_id_assoc]
      _ = f.hom ≫ ((doubleSingularChainBicomplex P).d (a' + 1) a').f b ≫ s₁ :=
        congrArg (f.hom ≫ ·) (doubleSingularChainTermSwap_d_other P a' b)
      _ = _ := by
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        rw [← Category.assoc f.hom, ← hr, Category.assoc]
  · rw [(doubleSingularCochainBicomplex P).shape q s hrel, HomologicalComplex.zero_f,
      ((doubleSingularCochainBicomplex P).X r).shape q s hrel, comp_zero, zero_comp]

/-- The actual double singular cochains exchange the two simplex degrees. -/
@[no_expose]
def doubleSingularCochainBicomplexSwap (P : PresheafWithTransfers.{v} k) :
    doubleSingularCochainBicomplex P ≅ (doubleSingularCochainBicomplex P).flip :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => HomologicalComplex.Hom.isoOfComponents (doubleSingularCochainTermSwap P q)
      (fun r s _ => doubleSingularCochainTermSwap_inner P q r s))
    (fun q s _ => HomologicalComplex.hom_ext _ _ (fun r =>
      doubleSingularCochainTermSwap_outer P q s r))

private theorem doubleSingularCochainTermSwap_natural
    {P Q : PresheafWithTransfers.{v} k} (f : P ⟶ Q) (q r : ℤ) :
    (doubleSingularCochainTermSwap P q r).hom ≫ ((S).map (((S).map f).f r)).f q =
      ((S).map (((S).map f).f q)).f r ≫ (doubleSingularCochainTermSwap Q q r).hom := by
  by_cases hq : 0 < q
  · exact (isZero_doubleSingularCochainTerm P q r (Or.inl hq)).eq_of_src _ _
  by_cases hr : 0 < r
  · exact (isZero_doubleSingularCochainTerm P q r (Or.inr hr)).eq_of_src _ _
  obtain ⟨a, ha⟩ := exists_singularDegree (show q ≤ 0 by omega)
  obtain ⟨b, hb⟩ := exists_singularDegree (show r ≤ 0 by omega)
  change 0 - (a : ℤ) = q at ha
  change 0 - (b : ℤ) = r at hb
  subst q
  subst r
  rw [doubleSingularCochainTermSwap_eq, doubleSingularCochainTermSwap_eq]
  let a₀ := 0 - (a : ℤ)
  let b₀ := 0 - (b : ℤ)
  let eP := doubleSingularPlacedTermIso P a₀ b₀ a b
    (singularDegree_eq_sub_natCast a) (singularDegree_eq_sub_natCast b)
  let eQ := doubleSingularPlacedTermIso Q a₀ b₀ a b
    (singularDegree_eq_sub_natCast a) (singularDegree_eq_sub_natCast b)
  let fP := doubleSingularPlacedTermIso P b₀ a₀ b a
    (singularDegree_eq_sub_natCast b) (singularDegree_eq_sub_natCast a)
  let fQ := doubleSingularPlacedTermIso Q b₀ a₀ b a
    (singularDegree_eq_sub_natCast b) (singularDegree_eq_sub_natCast a)
  let sP := (doubleSingularChainTermSwap P a b).hom
  let sQ := (doubleSingularChainTermSwap Q a b).hom
  let m := ((S).map (((S).map f).f a₀)).f b₀
  let m' := ((S).map (((S).map f).f b₀)).f a₀
  let m₀ := (singularComplexMap ((singularComplexMap f).f a)).f b
  let m₁ := (singularComplexMap ((singularComplexMap f).f b)).f a
  have hm : m ≫ eQ.hom = eP.hom ≫ m₀ :=
    doubleSingularPlacedTermIso_natural f a₀ b₀ a b
      (singularDegree_eq_sub_natCast a) (singularDegree_eq_sub_natCast b)
  have hm' : m' ≫ fQ.hom = fP.hom ≫ m₁ :=
    doubleSingularPlacedTermIso_natural f b₀ a₀ b a
      (singularDegree_eq_sub_natCast b) (singularDegree_eq_sub_natCast a)
  apply (cancel_mono fQ.hom).1
  change ((eP.hom ≫ sP ≫ fP.inv) ≫ m') ≫ fQ.hom =
    (m ≫ eQ.hom ≫ sQ ≫ fQ.inv) ≫ fQ.hom
  calc
    _ = eP.hom ≫ sP ≫ (fP.inv ≫ (m' ≫ fQ.hom)) := by
      simp only [Category.assoc]
    _ = eP.hom ≫ sP ≫ m₁ := by rw [hm', Iso.inv_hom_id_assoc]
    _ = eP.hom ≫ m₀ ≫ sQ :=
      congrArg (eP.hom ≫ ·) (doubleSingularChainTermSwap_natural f a b)
    _ = _ := by
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [← Category.assoc eP.hom, ← hm, Category.assoc]

/-- Take the two singular directions of the original presheaf functorially. -/
abbrev doubleSingularCochainBicomplexFunctor (k : Type u) [Field k] :
    PresheafWithTransfers.{v} k ⥤ HomologicalComplex₂ (PresheafWithTransfers.{v} k) c c :=
  (singularCoChains k) ⋙ (singularCoChains k).mapHomologicalComplex c

/-- The exchange of the two simplex factors is natural in the coefficient presheaf. -/
theorem doubleSingularCochainBicomplexSwap_natural
    {P Q : PresheafWithTransfers.{v} k} (f : P ⟶ Q) :
    (doubleSingularCochainBicomplexSwap P).hom ≫
        (flipFunctor (PresheafWithTransfers.{v} k) c c).map
          ((doubleSingularCochainBicomplexFunctor k).map f) =
      (doubleSingularCochainBicomplexFunctor k).map f ≫
        (doubleSingularCochainBicomplexSwap Q).hom := by
  ext q r : 2
  exact doubleSingularCochainTermSwap_natural f q r

/-- The component of the double-complex permutation is the original term exchange. -/
theorem doubleSingularCochainBicomplexSwap_hom_f_f
    (P : PresheafWithTransfers.{v} k) (q r : ℤ) :
    (((doubleSingularCochainBicomplexSwap P).hom).f q).f r =
      (doubleSingularCochainTermSwap P q r).hom := by
  unfold doubleSingularCochainBicomplexSwap
  rfl

private theorem doubleSingularChainTermSwap_unit (P : PresheafWithTransfers.{v} k) (q : ℕ) :
    (singularComplexMap (singularTermUnit P 0)).f q ≫
        (doubleSingularChainTermSwap P 0 q).hom = singularTermUnit (singularTerm P q) 0 := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext X
  let U := X.unop
  let T := Δ(0)
  let V := Δ(q)
  let b := (Cor.simplexProjection (k := k) 0).app (Cor.simplexProduct U q)
  let a := Cor.simplexExterior q ((Cor.simplexProjection (k := k) 0).app U)
  let s := (Cor.parameterProductSwapNatIso T V).hom.app U
  change transfer P b ≫ transfer P s = transfer P a
  have h : s ≫ b = a := by
    change ((Cor.graphFunctor k).map (productSwapLast U.toSmoothSite T V)) ≫
        ((Cor.graphFunctor k).map (productFst (product U.toSmoothSite V) T)) =
      Cor.simplexExterior q ((Cor.graphFunctor k).map (productFst U.toSmoothSite T))
    rw [← Functor.map_comp, Cor.simplexExterior_graph]
    exact (Cor.graphFunctor k).congr_map (productSwapLast_fst U.toSmoothSite T V)
  exact (transfer_comp P s b).symm.trans (congrArg (transfer P) h)

/-- Exchanging the two cochain directions exchanges their degree-zero sections. -/
theorem doubleSingularCochainTermSwap_unit (P : PresheafWithTransfers.{v} k) (q : ℤ) :
    ((S).map (singularZeroInclusion P)).f q ≫
        (doubleSingularCochainTermSwap P 0 q).hom =
      singularZeroInclusion ((singularCochainComplex P 0).X q) := by
  by_cases hq : 0 < q
  · exact (isZero_singularCochainComplex_X P 0 q hq).eq_of_src _ _
  obtain ⟨r, hr⟩ := exists_singularDegree (show q ≤ 0 by omega)
  change 0 - (r : ℤ) = q at hr
  subst q
  let q := 0 - (r : ℤ)
  let e := singularDegreeIso P q r (singularDegree_eq_sub_natCast r)
  let h₀ : (ComplexShape.embeddingUpIntLE 0).f 0 = 0 := singularDegree_eq_sub_natCast 0
  let b := doubleSingularPlacedTermIso P q 0 r 0 (singularDegree_eq_sub_natCast r) h₀
  let a := doubleSingularPlacedTermIso P 0 q 0 r h₀ (singularDegree_eq_sub_natCast r)
  let m := (singularComplexMap (singularTermUnit P 0)).f r
  have ha : ((S).map (singularZeroInclusion P)).f q ≫ a.hom = e.hom ≫ m := by
    let f := singularZeroInclusion P
    let E := (S₀) ⋙ HomologicalComplex.eval (PresheafWithTransfers.{v} k) d r
    let i := singularDegreeIso ((singularCochainComplex P 0).X 0) q r
      (singularDegree_eq_sub_natCast r)
    let e₀ := singularDegreeIso P 0 0 h₀
    have h : f ≫ e₀.hom = singularTermUnit P 0 := by
      change singularTermUnit P 0 ≫ (singularCochainXIso P 0 0).inv ≫
        (singularCochainXIso P 0 0).hom = _
      rw [Iso.inv_hom_id, Category.comp_id]
    have hf : ((S).map f).f q ≫ i.hom = e.hom ≫ E.map f :=
      singularDegreeIso_map f q r (singularDegree_eq_sub_natCast r)
    change ((S).map f).f q ≫ i.hom ≫ E.map e₀.hom = e.hom ≫ E.map (singularTermUnit P 0)
    calc
      _ = (((S).map f).f q ≫ i.hom) ≫ E.map e₀.hom := (Category.assoc _ _ _).symm
      _ = (e.hom ≫ E.map f) ≫ E.map e₀.hom := congrArg (· ≫ E.map e₀.hom) hf
      _ = e.hom ≫ E.map (f ≫ e₀.hom) :=
        (Category.assoc e.hom (E.map f) (E.map e₀.hom)).trans
          (congrArg (e.hom ≫ ·) (E.map_comp f e₀.hom).symm)
      _ = _ := congrArg (fun g => e.hom ≫ E.map g) h
  have hb : singularZeroInclusion ((singularCochainComplex P 0).X q) ≫ b.hom =
      e.hom ≫ singularTermUnit (singularTerm P r) 0 := by
    let Q := (singularCochainComplex P 0).X q
    change (singularTermUnit Q 0 ≫ (singularCochainXIso Q 0 0).inv) ≫
        (singularCochainXIso Q 0 0).hom ≫ (singularComplexMap e.hom).f 0 = _
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact (singularTermUnit_naturality e.hom 0).symm
  apply (cancel_mono b.hom).1
  have hs : (doubleSingularCochainTermSwap P 0 q).hom =
      a.hom ≫ (doubleSingularChainTermSwap P 0 r).hom ≫ b.inv := by
    exact congrArg Iso.hom (doubleSingularCochainTermSwap_eq P 0 r)
  rw [hs, Category.assoc, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    ← Category.assoc, ha, Category.assoc, doubleSingularChainTermSwap_unit, hb]

end AlgebraicGeometry.PresheafWithTransfers
