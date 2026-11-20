/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.SpectralSequence.WindowColimits
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.SpectralObject.Basic
import StacksFrontier.CategoryTheory.Abelian.SigmaExactness

/-!
# From closed-support spectral objects to coniveau spectral objects

For an arrow `b ⟶ a` in the reversed codimension order, take the colimit over
pairs of closed supports with bounds `b` and `a`. For two composable arrows,
the three window indices are final projections from one filtered flag index.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open OrderDual TopologicalSpace AlgebraicGeometry.Scheme

universe u w'

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k] (X : SmoothSite (Spec (CommRingCat.of k)))

local notation "CS" => Closeds X.left

/-- The inclusion of each closed support pair into the category of arrows of closed supports. -/
def coniveauSupportPairsToArrows (a b : ℕ) :
    ConiveauSupportPairs k X a b ⥤ ComposableArrows CS 1 where
  obj T := mk₁ (homOfLE T.2)
  map f := homMk₁ (homOfLE f.le.1) (homOfLE f.le.2) (Subsingleton.elim _ _)
  map_id _ := by apply hom_ext₁ <;> apply Subsingleton.elim
  map_comp _ _ := by apply hom_ext₁ <;> apply Subsingleton.elim

private def coniveauSupportTriplesToArrows (a b c : ℕ) :
    ConiveauSupportTriples k X a b c ⥤ ComposableArrows CS 2 where
  obj T := mk₂ (homOfLE T.small_le_middle) (homOfLE T.middle_le_large)
  map f := homMk₂ (homOfLE f.le.1) (homOfLE f.le.2.1) (homOfLE f.le.2.2)
    (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  map_id _ := by apply hom_ext₂ <;> apply Subsingleton.elim
  map_comp _ _ := by apply hom_ext₂ <;> apply Subsingleton.elim

variable [UnivLE.{u, w'}]
  (S : Abelian.SpectralObject AddCommGrpCat.{w'} (Closeds X.left))

/-- The diagram of the degree-`n` groups of a closed-support spectral object on a window. -/
abbrev closedSupportWindowDiagram (n : ℤ) (a b : ℕ) :
    ConiveauSupportPairs k X a b ⥤ AddCommGrpCat.{w'} :=
  coniveauSupportPairsToArrows k X a b ⋙ S.H n

local notation "D" => closedSupportWindowDiagram k X S

/-- Weaken the bounds in the window colimit of a closed-support spectral object. -/
def closedSupportWindowMap (n : ℤ) {a b a' b' : ℕ} (ha : a' ≤ a) (hb : b' ≤ b) :
    colimit (D n a b) ⟶ colimit (D n a' b') :=
  colimit.pre (D n a' b') (coniveauSupportPairsWeaken k X ha hb)

@[reassoc]
private theorem ι_closedSupportWindowMap (n : ℤ) {a b a' b' : ℕ}
    (ha : a' ≤ a) (hb : b' ≤ b) (T : ConiveauSupportPairs k X a b) :
    colimit.ι (D n a b) T ≫ closedSupportWindowMap k X S n ha hb =
      colimit.ι (D n a' b') ((coniveauSupportPairsWeaken k X ha hb).obj T) :=
  colimit.ι_pre (D n a' b') (coniveauSupportPairsWeaken k X ha hb) T

/-- The degree-`n` coniveau window groups, functorial by weakening bounds. -/
def closedSupportWindowFunctor (n : ℤ) : ComposableArrows ℕᵒᵈ 1 ⥤ AddCommGrpCat.{w'} where
  obj A := colimit (D n (ofDual A.right) (ofDual A.left))
  map f := closedSupportWindowMap k X S n (f.app 1).le (f.app 0).le
  map_id A := by
    apply colimit.hom_ext (F := D n (ofDual A.right) (ofDual A.left))
    intro T
    rw [Category.comp_id]
    exact ι_closedSupportWindowMap k X S n le_rfl le_rfl T
  map_comp {A B C} f g := by
    apply colimit.hom_ext (F := D n (ofDual A.right) (ofDual A.left))
    intro T
    rw [ι_closedSupportWindowMap, ι_closedSupportWindowMap_assoc, ι_closedSupportWindowMap]
    rfl

/-- The map on each pair of supports keeps that pair with the new bounds. -/
@[reassoc]
theorem ι_closedSupportWindowFunctor_map (n : ℤ) {A B : ComposableArrows ℕᵒᵈ 1}
    (f : A ⟶ B) (T : ConiveauSupportPairs k X (ofDual A.right) (ofDual A.left)) :
    colimit.ι (D n (ofDual A.right) (ofDual A.left)) T ≫
        (closedSupportWindowFunctor k X S n).map f =
      colimit.ι (D n (ofDual B.right) (ofDual B.left))
        ((coniveauSupportPairsWeaken k X (f.app 1).le (f.app 0).le).obj T) :=
  ι_closedSupportWindowMap k X S n (f.app 1).le (f.app 0).le T

section Flags

variable (a b c : ℕ)

local notation "L" => coniveauSupportTriplesLeft k X a b c
local notation "M" => coniveauSupportTriplesMiddle k X a b c
local notation "R" => coniveauSupportTriplesRight k X a b c
local notation "F" => coniveauSupportTriplesToArrows k X a b c

private abbrev flagFirstMap (n : ℤ) : L ⋙ D n b c ⟶ M ⋙ D n a c :=
  Functor.whiskerLeft F (Functor.whiskerRight (mapFunctorArrows CS 0 1 0 2 2) (S.H n))

private abbrev flagSecondMap (n : ℤ) : M ⋙ D n a c ⟶ R ⋙ D n a b :=
  Functor.whiskerLeft F (Functor.whiskerRight (mapFunctorArrows CS 0 2 1 2 2) (S.H n))

private abbrev flagBoundary (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) :
    R ⋙ D n₀ a b ⟶ L ⋙ D n₁ b c :=
  Functor.whiskerLeft F (S.δ' n₀ n₁ hn₁)

private def windowBoundary (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) :
    colimit (D n₀ a b) ⟶ colimit (D n₁ b c) :=
  (Functor.Final.colimitIso R (D n₀ a b)).inv ≫
    colimMap (flagBoundary k X S a b c n₀ n₁ hn₁) ≫ colimit.pre (D n₁ b c) L

@[reassoc]
private theorem ι_windowBoundary (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁)
    (T : ConiveauSupportTriples k X a b c) :
    colimit.ι (D n₀ a b) ((R).obj T) ≫ windowBoundary k X S a b c n₀ n₁ hn₁ =
      S.δ (homOfLE T.small_le_middle) (homOfLE T.middle_le_large) n₀ n₁ hn₁ ≫
        colimit.ι (D n₁ b c) ((L).obj T) := by
  simp only [windowBoundary, Functor.Final.ι_colimitIso_inv_assoc, ι_colimMap_assoc, colimit.ι_pre]
  rfl

end Flags

section FinalColimits

variable {J A B C : Type u} [Category.{u} J] [Category.{u} A] [Category.{u} B] [Category.{u} C]

private theorem colimit_hom_ext_of_final (P : J ⥤ A) [P.Final]
    (G : A ⥤ AddCommGrpCat.{w'}) {V : AddCommGrpCat.{w'}} {f g : colimit G ⟶ V}
    (h : ∀ j, colimit.ι G (P.obj j) ≫ f = colimit.ι G (P.obj j) ≫ g) : f = g := by
  rw [← cancel_epi (Functor.Final.colimitIso P G).hom]
  apply colimit.hom_ext
  intro j
  simpa only [Category.assoc, Functor.Final.ι_colimitIso_hom_assoc] using h j

private theorem exact_of_filtered_windows [IsFiltered J]
    (P : J ⥤ A) (Q : J ⥤ B) (R : J ⥤ C) [P.Final] [Q.Final] [R.Final]
    {G₁ : A ⥤ AddCommGrpCat.{w'}} {G₂ : B ⥤ AddCommGrpCat.{w'}}
    {G₃ : C ⥤ AddCommGrpCat.{w'}}
    (f : P ⋙ G₁ ⟶ Q ⋙ G₂) (g : Q ⋙ G₂ ⟶ R ⋙ G₃)
    (h : ∀ j, (mk₂ (f.app j) (g.app j)).Exact)
    {f' : colimit G₁ ⟶ colimit G₂} {g' : colimit G₂ ⟶ colimit G₃}
    (hf : ∀ j, colimit.ι G₁ (P.obj j) ≫ f' = f.app j ≫ colimit.ι G₂ (Q.obj j))
    (hg : ∀ j, colimit.ι G₂ (Q.obj j) ≫ g' = g.app j ≫ colimit.ι G₃ (R.obj j)) :
    (mk₂ f' g').Exact := by
  let T := ShortComplex.mk f g (by
    apply NatTrans.ext
    funext j
    exact (h j).zero 0)
  have hT : T.Exact := Stacks.SigmaExactness.exact_of_app T fun j ↦ (h j).exact 0
  have hc := hT.map (colim (J := J) (C := AddCommGrpCat.{w'}))
  refine ComposableArrows.exact_of_iso (isoMk₂
    (Functor.Final.colimitIso P G₁) (Functor.Final.colimitIso Q G₂)
    (Functor.Final.colimitIso R G₃) ?_ ?_) hc.exact_toComposableArrows
  · change colimMap f ≫ (Functor.Final.colimitIso Q G₂).hom =
      (Functor.Final.colimitIso P G₁).hom ≫ f'
    apply colimit.hom_ext
    intro j
    simpa only [Category.assoc, Functor.Final.ι_colimitIso_hom_assoc, ι_colimMap_assoc,
      Functor.Final.ι_colimitIso_hom] using (hf j).symm
  · change colimMap g ≫ (Functor.Final.colimitIso R G₃).hom =
      (Functor.Final.colimitIso Q G₂).hom ≫ g'
    apply colimit.hom_ext
    intro j
    simpa only [Category.assoc, Functor.Final.ι_colimitIso_hom_assoc, ι_colimMap_assoc,
      Functor.Final.ι_colimitIso_hom] using (hg j).symm

end FinalColimits

local notation "Hwin" => closedSupportWindowFunctor k X S
local notation "F₀" => functorArrows (ℕᵒᵈ) 0 1 2
local notation "F₂" => functorArrows (ℕᵒᵈ) 1 2 2
local notation "a[" A "]" => ofDual (Functor.obj A 2)
local notation "b[" A "]" => ofDual (Functor.obj A 1)
local notation "c[" A "]" => ofDual (Functor.obj A 0)

/-- The natural connecting maps on all coniveau windows of a closed-support spectral object. -/
@[no_expose]
def closedSupportWindowBoundary (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) :
    F₂ ⋙ Hwin n₀ ⟶ F₀ ⋙ Hwin n₁ where
  app A := windowBoundary k X S a[A] b[A] c[A] n₀ n₁ hn₁
  naturality {A B} f := by
    change closedSupportWindowMap k X S n₀ (f.app 2).le (f.app 1).le ≫
        windowBoundary k X S a[B] b[B] c[B] n₀ n₁ hn₁ =
      windowBoundary k X S a[A] b[A] c[A] n₀ n₁ hn₁ ≫
        closedSupportWindowMap k X S n₁ (f.app 1).le (f.app 0).le
    apply colimit_hom_ext_of_final (coniveauSupportTriplesRight k X a[A] b[A] c[A])
      (D n₀ a[A] b[A])
    intro T
    let T' := coniveauSupportTriplesWeaken k X (f.app 2).le (f.app 1).le (f.app 0).le T
    rw [ι_closedSupportWindowMap_assoc, ι_windowBoundary_assoc k X S a[A] b[A] c[A] n₀ n₁ hn₁ T,
      ι_closedSupportWindowMap]
    exact ι_windowBoundary k X S a[B] b[B] c[B] n₀ n₁ hn₁ T'

private theorem ι_firstWindowMap (n : ℤ) (A : ComposableArrows ℕᵒᵈ 2)
    (T : ConiveauSupportTriples k X a[A] b[A] c[A]) :
    colimit.ι (D n b[A] c[A]) ((coniveauSupportTriplesLeft k X _ _ _).obj T) ≫
        (Hwin n).map ((mapFunctorArrows (ℕᵒᵈ) 0 1 0 2 2).app A) =
      (flagFirstMap k X S a[A] b[A] c[A] n).app T ≫
        colimit.ι (D n a[A] c[A]) ((coniveauSupportTriplesMiddle k X _ _ _).obj T) := by
  let P := coniveauSupportTriplesLeft k X a[A] b[A] c[A]
  let Q := coniveauSupportTriplesMiddle k X a[A] b[A] c[A]
  change _ ≫ closedSupportWindowMap k X S n (A.map' 1 2).le (le_refl c[A]) = _
  rw [ι_closedSupportWindowMap]
  let f : (coniveauSupportPairsWeaken k X (A.map' 1 2).le le_rfl).obj (P.obj T) ⟶ Q.obj T :=
    homOfLE ⟨le_rfl, T.middle_le_large⟩
  exact (colimit.w (D n a[A] c[A]) f).symm

private theorem ι_secondWindowMap (n : ℤ) (A : ComposableArrows ℕᵒᵈ 2)
    (T : ConiveauSupportTriples k X a[A] b[A] c[A]) :
    colimit.ι (D n a[A] c[A]) ((coniveauSupportTriplesMiddle k X _ _ _).obj T) ≫
        (Hwin n).map ((mapFunctorArrows (ℕᵒᵈ) 0 2 1 2 2).app A) =
      (flagSecondMap k X S a[A] b[A] c[A] n).app T ≫
        colimit.ι (D n a[A] b[A]) ((coniveauSupportTriplesRight k X _ _ _).obj T) := by
  let P := coniveauSupportTriplesMiddle k X a[A] b[A] c[A]
  let Q := coniveauSupportTriplesRight k X a[A] b[A] c[A]
  change _ ≫ closedSupportWindowMap k X S n (le_refl a[A]) (A.map' 0 1).le = _
  rw [ι_closedSupportWindowMap]
  let f : (coniveauSupportPairsWeaken k X le_rfl (A.map' 0 1).le).obj (P.obj T) ⟶ Q.obj T :=
    homOfLE ⟨T.small_le_middle, le_rfl⟩
  exact (colimit.w (D n a[A] b[A]) f).symm

/-- The coniveau spectral object formed from a spectral object on closed supports by
taking filtered colimits of its windows. -/
def closedSupportWindowSpectralObject : Abelian.SpectralObject AddCommGrpCat.{w'} ℕᵒᵈ where
  H := Hwin
  δ' := closedSupportWindowBoundary k X S
  exact₁' n₀ n₁ hn₁ A := by
    let := coniveauSupportTriplesLeft_final k X (a := a[A]) (b := b[A]) (c := c[A]) (A.map' 1 2).le
    let := coniveauSupportTriplesMiddle_final k X (a := a[A]) (b := b[A]) (c := c[A])
      (A.map' 0 1).le
    exact exact_of_filtered_windows (coniveauSupportTriplesRight k X a[A] b[A] c[A])
      (coniveauSupportTriplesLeft k X a[A] b[A] c[A])
      (coniveauSupportTriplesMiddle k X a[A] b[A] c[A])
      (flagBoundary k X S a[A] b[A] c[A] n₀ n₁ hn₁) (flagFirstMap k X S a[A] b[A] c[A] n₁)
      (fun T ↦ S.exact₁' n₀ n₁ hn₁ ((coniveauSupportTriplesToArrows k X _ _ _).obj T))
      (ι_windowBoundary k X S a[A] b[A] c[A] n₀ n₁ hn₁) (ι_firstWindowMap k X S n₁ A)
  exact₂' n A := by
    let := coniveauSupportTriplesLeft_final k X (a := a[A]) (b := b[A]) (c := c[A]) (A.map' 1 2).le
    let := coniveauSupportTriplesMiddle_final k X (a := a[A]) (b := b[A]) (c := c[A])
      (A.map' 0 1).le
    exact exact_of_filtered_windows (coniveauSupportTriplesLeft k X a[A] b[A] c[A])
      (coniveauSupportTriplesMiddle k X a[A] b[A] c[A])
      (coniveauSupportTriplesRight k X a[A] b[A] c[A])
      (flagFirstMap k X S a[A] b[A] c[A] n) (flagSecondMap k X S a[A] b[A] c[A] n)
      (fun T ↦ S.exact₂' n ((coniveauSupportTriplesToArrows k X _ _ _).obj T))
      (ι_firstWindowMap k X S n A) (ι_secondWindowMap k X S n A)
  exact₃' n₀ n₁ hn₁ A := by
    let := coniveauSupportTriplesLeft_final k X (a := a[A]) (b := b[A]) (c := c[A]) (A.map' 1 2).le
    let := coniveauSupportTriplesMiddle_final k X (a := a[A]) (b := b[A]) (c := c[A])
      (A.map' 0 1).le
    exact exact_of_filtered_windows (coniveauSupportTriplesMiddle k X a[A] b[A] c[A])
      (coniveauSupportTriplesRight k X a[A] b[A] c[A])
      (coniveauSupportTriplesLeft k X a[A] b[A] c[A])
      (flagSecondMap k X S a[A] b[A] c[A] n₀) (flagBoundary k X S a[A] b[A] c[A] n₀ n₁ hn₁)
      (fun T ↦ S.exact₃' n₀ n₁ hn₁ ((coniveauSupportTriplesToArrows k X _ _ _).obj T))
      (ι_secondWindowMap k X S n₀ A) (ι_windowBoundary k X S a[A] b[A] c[A] n₀ n₁ hn₁)

/-- The coniveau boundary on a generator is the boundary on its flag of closed supports. -/
@[reassoc]
theorem ι_closedSupportWindowSpectralObject_δ (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁)
    {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (T : ConiveauSupportTriples k X a b c) :
    colimit.ι (D n₀ a b) ((coniveauSupportTriplesRight k X a b c).obj T) ≫
      (closedSupportWindowSpectralObject k X S).δ
        (homOfLE (show toDual c ≤ toDual b from hbc))
        (homOfLE (show toDual b ≤ toDual a from hab)) n₀ n₁ hn₁ =
      S.δ (homOfLE T.small_le_middle) (homOfLE T.middle_le_large) n₀ n₁ hn₁ ≫
        colimit.ι (D n₁ b c) ((coniveauSupportTriplesLeft k X a b c).obj T) :=
  ι_windowBoundary k X S a b c n₀ n₁ hn₁ T

end AlgebraicGeometry.MotivicHomotopy
