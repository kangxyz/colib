/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.AlgebraicGeometry.Scheme.QuasiCompactOpenPairPolynomialLaurent
public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedPairPullback
public import Colib.KTheory.Bass.TwoChart
public import Colib.KTheory.Waldhausen.Additivity.GroupFormula
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup

/-!
Source: `Quillen/AlgebraicGeometry/PerfectComplexes/Bass/SupportedGroups.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

Genuine supported Bass negative groups on qc scheme/open pairs. Index n denotes K_{-n}; degree zero
retains the unchanged original supported perfect K0 and all arbitrary pair pullbacks. Successors are
the actual two-chart cokernels, with original representatives, exact presentation and unique
prescribed descent. Opens need not be qc. Negative localization is a separate theorem.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.Bass
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules

/-- The commutative group structure on original supported K0 supplied by additivity. -/
local instance supportedKZeroCommGroup (A : QuasiCompactOpenPairs.{u}) :
    CommGroup (PerfectSupportedK A.obj.hom 0) :=
  CategoryTheory.Waldhausen.Additivity.KCommGroup (perfectSupportedWaldhausen A.obj.hom) 0

/-- The unchanged original supported K0 and arbitrary commutative pair pullbacks. -/
def supportedKZeroMultiplicativeFunctor : QuasiCompactOpenPairs.{u}ᵒᵖ ⥤ CommGrpCat.{u+1} where
  obj A := .of (PerfectSupportedK A.unop.obj.hom 0)
  map f := CommGrpCat.ofHom (perfectSupportedKPullback f.unop 0)
  map_id A := by apply CommGrpCat.hom_ext; exact perfectSupportedKPullback_id A.unop 0
  map_comp f g := by apply CommGrpCat.hom_ext; exact perfectSupportedKPullback_comp g.unop f.unop 0

/-- The additive form of the original supported K0 functor. -/
def supportedKZeroFunctor : QuasiCompactOpenPairs.{u}ᵒᵖ ⥤ AddCommGrpCat.{u+1} :=
  supportedKZeroMultiplicativeFunctor ⋙ CommGrpCat.toAddCommGrp

/-- The unchanged supported perfect K-groups, in additive notation, in every connective degree. -/
def supportedKFunctor (n : ℕ) : QuasiCompactOpenPairs.{u}ᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj A :=
    letI := CategoryTheory.Waldhausen.Additivity.KCommGroup
      (perfectSupportedWaldhausen A.unop.obj.hom) n
    .of (Additive (PerfectSupportedK A.unop.obj.hom n))
  map {A B} f :=
    letI := CategoryTheory.Waldhausen.Additivity.KCommGroup
      (perfectSupportedWaldhausen A.unop.obj.hom) n
    letI := CategoryTheory.Waldhausen.Additivity.KCommGroup
      (perfectSupportedWaldhausen B.unop.obj.hom) n
    AddCommGrpCat.ofHom (perfectSupportedKPullback f.unop n).toAdditive
  map_id A := by
    apply AddCommGrpCat.hom_ext
    exact congrArg MonoidHom.toAdditive (perfectSupportedKPullback_id A.unop n)
  map_comp f g := by
    apply AddCommGrpCat.hom_ext
    exact congrArg MonoidHom.toAdditive (perfectSupportedKPullback_comp g.unop f.unop n)

/-- Bass recursion on actual scheme/open-support pairs. The index n means K_{-n}. -/
def supportedNegativeKFunctor : ℕ → QuasiCompactOpenPairs.{u}ᵒᵖ ⥤ AddCommGrpCat.{u+1}
  | 0 => supportedKZeroFunctor
  | n+1 => KTheory.Bass.TwoChart.contraction (NatTrans.op Scheme.Bass.pairPlus)
      (NatTrans.op Scheme.Bass.pairMinus) (supportedNegativeKFunctor n)

/-- The supported Bass group K_{-n} of an actual quasi-compact open pair. -/
abbrev supportedNegativeK (A : QuasiCompactOpenPairs.{u}) (n : ℕ) : AddCommGrpCat.{u+1} :=
  (supportedNegativeKFunctor n).obj (op A)

/-- Contravariant pullback on the iterated supported Bass groups. -/
abbrev supportedNegativeKPullback {A B : QuasiCompactOpenPairs.{u}} (f : A ⟶ B) (n : ℕ) :
    supportedNegativeK B n ⟶ supportedNegativeK A n := (supportedNegativeKFunctor n).map f.op

@[simp] lemma supportedNegativeKPullback_id (A : QuasiCompactOpenPairs.{u}) (n : ℕ) :
    supportedNegativeKPullback (𝟙 A) n = 𝟙 _ := (supportedNegativeKFunctor n).map_id _

@[simp] lemma supportedNegativeKPullback_comp {A B C : QuasiCompactOpenPairs.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (n : ℕ) :
    supportedNegativeKPullback (f ≫ g) n =
      supportedNegativeKPullback g n ≫ supportedNegativeKPullback f n :=
  (supportedNegativeKFunctor n).map_comp g.op f.op

@[simp] lemma supportedNegativeKPullback_zero {A B : QuasiCompactOpenPairs.{u}}
    (f : A ⟶ B) (a : PerfectSupportedK B.obj.hom 0) :
    supportedNegativeKPullback f 0 (Additive.ofMul a) =
      Additive.ofMul (perfectSupportedKPullback f 0 a) := rfl

/-- The original relative Laurent representative defines the next supported negative group. -/
def supportedNegativeKπ (A : QuasiCompactOpenPairs.{u}) (n : ℕ) :
    supportedNegativeK (Scheme.Bass.pairLaurentFunctor.obj A) n ⟶ supportedNegativeK A (n+1) :=
  (KTheory.Bass.TwoChart.contractionπ (NatTrans.op Scheme.Bass.pairPlus)
    (NatTrans.op Scheme.Bass.pairMinus) (supportedNegativeKFunctor n)).app (op A)

@[reassoc] lemma supportedNegativeKπ_naturality {A B : QuasiCompactOpenPairs.{u}}
    (f : A ⟶ B) (n : ℕ) :
    supportedNegativeKPullback (Scheme.Bass.pairLaurentFunctor.map f) n ≫ supportedNegativeKπ A n =
      supportedNegativeKπ B n ≫ supportedNegativeKPullback f (n+1) :=
  (KTheory.Bass.TwoChart.contractionπ (NatTrans.op Scheme.Bass.pairPlus)
    (NatTrans.op Scheme.Bass.pairMinus) (supportedNegativeKFunctor n)).naturality f.op

lemma supportedNegativeKπ_surjective (A : QuasiCompactOpenPairs.{u}) (n : ℕ) :
    Function.Surjective (supportedNegativeKπ A n) :=
  KTheory.Bass.TwoChart.contractionπ_surjective _ _ _ _

lemma supportedNegativeKπ_eq_zero_iff (A : QuasiCompactOpenPairs.{u}) (n : ℕ)
    (x : supportedNegativeK (Scheme.Bass.pairLaurentFunctor.obj A) n) :
    supportedNegativeKπ A n x = 0 ↔
      ∃ a b : supportedNegativeK (Scheme.Bass.pairPolynomialFunctor.obj A) n,
        supportedNegativeKPullback (Scheme.Bass.pairPlus.app A) n a -
          supportedNegativeKPullback (Scheme.Bass.pairMinus.app A) n b = x :=
  KTheory.Bass.TwoChart.contractionπ_eq_zero_iff _ _ _ _ _

lemma supportedNegativeK_exact (A : QuasiCompactOpenPairs.{u}) (n : ℕ) :
    (ShortComplex.mk
      (KTheory.Bass.TwoChart.polynomialDifference (NatTrans.op Scheme.Bass.pairPlus)
        (NatTrans.op Scheme.Bass.pairMinus) (supportedNegativeKFunctor n) (op A))
      (supportedNegativeKπ A n)
      (KTheory.Bass.TwoChart.polynomialDifference_contractionπ _ _ _ _)).Exact :=
  KTheory.Bass.TwoChart.contraction_exact _ _ _ _

instance supportedNegativeKπ_epi (A : QuasiCompactOpenPairs.{u}) (n : ℕ) :
    Epi (supportedNegativeKπ A n) := KTheory.Bass.TwoChart.contractionπ_epi _ _ _ _

/-- Unique descent of a prescribed Laurent map annihilating both actual supported chart maps. -/
def supportedNegativeKDesc (A : QuasiCompactOpenPairs.{u}) (n : ℕ) {B : AddCommGrpCat.{u + 1}}
    (f : supportedNegativeK (Scheme.Bass.pairLaurentFunctor.obj A) n ⟶ B)
    (hp : supportedNegativeKPullback (Scheme.Bass.pairPlus.app A) n ≫ f = 0)
    (hm : supportedNegativeKPullback (Scheme.Bass.pairMinus.app A) n ≫ f = 0) :
    supportedNegativeK A (n+1) ⟶ B :=
  KTheory.Bass.TwoChart.contractionDescOfCharts _ _ _ _ f hp hm

@[reassoc (attr := simp)] lemma supportedNegativeKπ_desc (A : QuasiCompactOpenPairs.{u}) (n : ℕ)
    {B : AddCommGrpCat.{u + 1}}
    (f : supportedNegativeK (Scheme.Bass.pairLaurentFunctor.obj A) n ⟶ B)
    (hp : supportedNegativeKPullback (Scheme.Bass.pairPlus.app A) n ≫ f = 0)
    (hm : supportedNegativeKPullback (Scheme.Bass.pairMinus.app A) n ≫ f = 0) :
    supportedNegativeKπ A n ≫ supportedNegativeKDesc A n f hp hm = f :=
  KTheory.Bass.TwoChart.contractionπ_descOfCharts (NatTrans.op Scheme.Bass.pairPlus)
    (NatTrans.op Scheme.Bass.pairMinus) (supportedNegativeKFunctor n) (op A) f hp hm

lemma supportedNegativeKDesc_unique (A : QuasiCompactOpenPairs.{u}) (n : ℕ)
    {B : AddCommGrpCat.{u + 1}}
    (f : supportedNegativeK (Scheme.Bass.pairLaurentFunctor.obj A) n ⟶ B)
    (hp : supportedNegativeKPullback (Scheme.Bass.pairPlus.app A) n ≫ f = 0)
    (hm : supportedNegativeKPullback (Scheme.Bass.pairMinus.app A) n ≫ f = 0)
    (g : supportedNegativeK A (n + 1) ⟶ B) (hg : supportedNegativeKπ A n ≫ g = f) :
    g = supportedNegativeKDesc A n f hp hm := by
  exact (cancel_epi (supportedNegativeKπ A n)).mp (hg.trans (supportedNegativeKπ_desc A n f hp
    hm).symm)

end AlgebraicGeometry.Scheme.Bass

end

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Bass/SupportedGroups.lean:38"
  "adaptation" "Original supported Bass quotient and its unchanged maps."]
  AlgebraicGeometry.Scheme.Bass.supportedKZeroMultiplicativeFunctor

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Bass/SupportedGroups.lean:45"
  "adaptation" "Original supported Bass quotient and its unchanged maps."]
  AlgebraicGeometry.Scheme.Bass.supportedKZeroFunctor

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Bass/SupportedGroups.lean:49"
  "adaptation" "Original supported Bass quotient and its unchanged maps."]
  AlgebraicGeometry.Scheme.Bass.supportedNegativeKFunctor

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Bass/SupportedGroups.lean:55"
  "adaptation" "Original supported Bass quotient and its unchanged maps."]
  AlgebraicGeometry.Scheme.Bass.supportedNegativeK

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Bass/SupportedGroups.lean:59"
  "adaptation" "Original supported Bass quotient and its unchanged maps."]
  AlgebraicGeometry.Scheme.Bass.supportedNegativeKPullback

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Bass/SupportedGroups.lean:62"
  "adaptation" "Original supported Bass quotient and its unchanged maps."]
  AlgebraicGeometry.Scheme.Bass.supportedNegativeKPullback_id

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Bass/SupportedGroups.lean:65"
  "adaptation" "Original supported Bass quotient and its unchanged maps."]
  AlgebraicGeometry.Scheme.Bass.supportedNegativeKPullback_comp

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Bass/SupportedGroups.lean:71"
  "adaptation" "Original supported Bass quotient and its unchanged maps."]
  AlgebraicGeometry.Scheme.Bass.supportedNegativeKPullback_zero

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Bass/SupportedGroups.lean:77"
  "adaptation" "Original supported Bass quotient and its unchanged maps."]
  AlgebraicGeometry.Scheme.Bass.supportedNegativeKπ

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Bass/SupportedGroups.lean:82"
  "adaptation" "Original supported Bass quotient and its unchanged maps."]
  AlgebraicGeometry.Scheme.Bass.supportedNegativeKπ_naturality

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Bass/SupportedGroups.lean:89"
  "adaptation" "Original supported Bass quotient and its unchanged maps."]
  AlgebraicGeometry.Scheme.Bass.supportedNegativeKπ_surjective

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Bass/SupportedGroups.lean:93"
  "adaptation" "Original supported Bass quotient and its unchanged maps."]
  AlgebraicGeometry.Scheme.Bass.supportedNegativeKπ_eq_zero_iff

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Bass/SupportedGroups.lean:101"
  "adaptation" "Original supported Bass quotient and its unchanged maps."]
  AlgebraicGeometry.Scheme.Bass.supportedNegativeK_exact

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Bass/SupportedGroups.lean:109"
  "adaptation" "Original supported Bass quotient and its unchanged maps."]
  AlgebraicGeometry.Scheme.Bass.supportedNegativeKπ_epi

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Bass/SupportedGroups.lean:113"
  "adaptation" "Original supported Bass quotient and its unchanged maps."]
  AlgebraicGeometry.Scheme.Bass.supportedNegativeKDesc

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Bass/SupportedGroups.lean:120"
  "adaptation" "Original supported Bass quotient and its unchanged maps."]
  AlgebraicGeometry.Scheme.Bass.supportedNegativeKπ_desc

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Bass/SupportedGroups.lean:129"
  "adaptation" "Original supported Bass quotient and its unchanged maps."]
  AlgebraicGeometry.Scheme.Bass.supportedNegativeKDesc_unique
