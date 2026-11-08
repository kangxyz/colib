/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
Implementation provenance: adapted from the corresponding
`Quillen/Aglib/Algebra/Homology` file at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Literal homotopy pullbacks of cochain complexes

The mapping cocone of `biprod.desc f (-g)` supplies actual projections and a
canonical homotopy between their composites. Any genuinely homotopy-commuting
pair lifts with strict projection equations. Each projection has an explicit
section in every degree; no chain-level section is asserted.

The ambient abelian category may have independent object and morphism universes.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CochainComplex.HomComplex
attribute [local instance] Abelian.hasFiniteBiproducts
namespace CochainComplex
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A B T : CochainComplex C ℤ} (f : A ⟶ T) (g : B ⟶ T)

/-- The literal mapping-cocone homotopy pullback of two actual chain maps. -/
def homotopyPullback : CochainComplex C ℤ :=
  CochainComplex.mappingCocone (biprod.desc f (-g))

/-- The original first projection. -/
def homotopyPullbackFst : homotopyPullback f g ⟶ A :=
  CochainComplex.mappingCocone.fst (biprod.desc f (-g)) ≫ biprod.fst

/-- The original second projection. -/
def homotopyPullbackSnd : homotopyPullback f g ⟶ B :=
  CochainComplex.mappingCocone.fst (biprod.desc f (-g)) ≫ biprod.snd

/-- A genuinely homotopy-commuting pair lifts to the actual mapping cocone;
its two projection equations are strictly equalities of chain maps. -/
def homotopyPullbackLift {M : CochainComplex C ℤ} (a : M ⟶ A) (b : M ⟶ B)
    (H : Homotopy (a ≫ f) (b ≫ g)) : M ⟶ homotopyPullback f g :=
  CochainComplex.mappingCocone.lift (biprod.desc f (-g)) (biprod.lift a b)
    (Cochain.ofHomotopy H.symm) (by
      rw [δ_ofHomotopy, biprod.lift_desc]
      simp only [Preadditive.comp_neg, ← sub_eq_add_neg, Cochain.ofHom_sub]
      abel)

@[reassoc (attr := simp)]
lemma homotopyPullbackLift_fst {M : CochainComplex C ℤ} (a : M ⟶ A) (b : M ⟶ B)
    (H : Homotopy (a ≫ f) (b ≫ g)) :
    homotopyPullbackLift f g a b H ≫ homotopyPullbackFst f g = a := by
  simp [homotopyPullbackLift, homotopyPullbackFst, ← Category.assoc]

@[reassoc (attr := simp)]
lemma homotopyPullbackLift_snd {M : CochainComplex C ℤ} (a : M ⟶ A) (b : M ⟶ B)
    (H : Homotopy (a ≫ f) (b ≫ g)) :
    homotopyPullbackLift f g a b H ≫ homotopyPullbackSnd f g = b := by
  simp [homotopyPullbackLift, homotopyPullbackSnd, ← Category.assoc]

/-- The first actual projection is split epic in every original degree. -/
def homotopyPullbackFstSplitEpi (i : ℤ) : SplitEpi ((homotopyPullbackFst f g).f i) where
  section_ := (biprod.inl : A ⟶ A ⊞ B).f i ≫
    (CochainComplex.mappingCocone.inl (biprod.desc f (-g))).v i i (add_zero i)
  id := by
    simp only [homotopyPullbackFst, HomologicalComplex.comp_f, Category.assoc,
      CochainComplex.mappingCocone.inl_v_fst_f_assoc]
    change (biprod.inl ≫ biprod.fst : A ⟶ A).f i = 𝟙 _
    simp

/-- The second actual projection is split epic in every original degree. -/
def homotopyPullbackSndSplitEpi (i : ℤ) : SplitEpi ((homotopyPullbackSnd f g).f i) where
  section_ := (biprod.inr : B ⟶ A ⊞ B).f i ≫
    (CochainComplex.mappingCocone.inl (biprod.desc f (-g))).v i i (add_zero i)
  id := by
    simp only [homotopyPullbackSnd, HomologicalComplex.comp_f, Category.assoc,
      CochainComplex.mappingCocone.inl_v_fst_f_assoc]
    change (biprod.inr ≫ biprod.snd : B ⟶ B).f i = 𝟙 _
    simp

lemma mappingCocone_δ_snd {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    δ (-1) 0 (CochainComplex.mappingCocone.snd φ) +
      Cochain.ofHom (CochainComplex.mappingCocone.fst φ ≫ φ) = 0 := by
  simp only [CochainComplex.mappingCocone.snd, CochainComplex.mappingCocone.fst,
    Cochain.δ_leftShift (CochainComplex.mappingCone.snd φ) (-1) (-1) 0 (by omega) 1 (by omega),
    CochainComplex.mappingCone.δ_snd, Cochain.leftShift_neg,
    Cochain.leftShift_comp_zero_cochain, Cochain.ofHom_comp, Cochain.ofHom_neg,
    Cocycle.cochain_ofHom_homOf_eq_coe]
  simp

/-- The actual mapping cocone carries its canonical null-homotopy. -/
def mappingCoconeCompHomotopy {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    Homotopy (CochainComplex.mappingCocone.fst φ ≫ φ) 0 :=
  (Cochain.equivHomotopy _ _).symm ⟨-CochainComplex.mappingCocone.snd φ, by
    simpa only [δ_neg, Cochain.ofHom_zero, add_zero] using
      eq_neg_of_add_eq_zero_right (mappingCocone_δ_snd φ)⟩

/-- The original two homotopy-pullback projections commute by a constructed
homotopy. The pullback lift then rectifies any use of this homotopy strictly. -/
def homotopyPullbackProjectionHomotopy {A B T : CochainComplex C ℤ}
    (f : A ⟶ T) (g : B ⟶ T) :
    Homotopy (homotopyPullbackFst f g ≫ f) (homotopyPullbackSnd f g ≫ g) := by
  have he : (homotopyPullbackFst f g ≫ f) - (homotopyPullbackSnd f g ≫ g) =
      CochainComplex.mappingCocone.fst (biprod.desc f (-g)) ≫ biprod.desc f (-g) := by
    simp only [homotopyPullbackFst, homotopyPullbackSnd, Category.assoc]
    rw [← Preadditive.comp_sub]
    congr 1
    apply biprod.hom_ext' <;> simp [Preadditive.comp_sub]
  exact Homotopy.equivSubZero.symm
    ((Homotopy.ofEq he).trans (mappingCoconeCompHomotopy (biprod.desc f (-g))))

end CochainComplex
