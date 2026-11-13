/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import StacksFrontier.Algebra.Homology.HomotopyCategory.BoundedStupidDevissage
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import StacksFrontier.CategoryTheory.Triangulated.ComponentwiseInvertibility
import StacksFrontier.Homology.KFlat.BifunctorTruncationGE

/-!
# The finite truncation test on the bounded-above derived category

The original degreewise split truncation triangles lift through the
full bounded-above inclusion. This gives a test for a natural
transformation whose source is the bounded-above derived category.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open HomologicalComplex ComplexShape StacksDraft.StupidTruncation

namespace DerivedCategory.Minus

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]

/-- A strictly bounded-above cochain complex viewed in the native
bounded-above derived category. -/
def ofCochainComplex (K : CochainComplex A ℤ) (b : ℤ) [K.IsStrictlyLE b] : Minus A :=
  ⟨Q.obj K, b, inferInstance⟩

/-- The original degreewise split truncation triangle with the supplied
bounds on its three cochain complexes. -/
private def triangleOfSES (S : ShortComplex (CochainComplex A ℤ)) (hS : S.ShortExact)
    (a b c : ℤ) [S.X₁.IsStrictlyLE a] [S.X₂.IsStrictlyLE b] [S.X₃.IsStrictlyLE c] :
    Triangle (Minus A) := by
  let X := ofCochainComplex S.X₁ a
  let Y := ofCochainComplex S.X₂ b
  let Z := ofCochainComplex S.X₃ c
  let h := (DerivedCategory.triangleOfSES hS).mor₃
  exact Triangle.mk (ObjectProperty.homMk (X := X) (Y := Y) (Q.map S.f))
    (ObjectProperty.homMk (X := Y) (Y := Z) (Q.map S.g))
    (ObjectProperty.homMk (X := Z) (Y := X⟦(1 : ℤ)⟧)
      (h ≫ (Minus.ι.commShiftIso (1 : ℤ)).inv.app X))

private theorem triangleOfSES_distinguished (S : ShortComplex (CochainComplex A ℤ))
    (hS : S.ShortExact) (a b c : ℤ) [S.X₁.IsStrictlyLE a] [S.X₂.IsStrictlyLE b]
    [S.X₃.IsStrictlyLE c] :
    triangleOfSES S hS a b c ∈ distTriang (Minus A) := by
  let X := ofCochainComplex S.X₁ a
  let T := DerivedCategory.triangleOfSES hS
  let U := triangleOfSES S hS a b c
  let ι : Minus A ⥤ DerivedCategory A := Minus.ι
  let d := (ι.commShiftIso (1 : ℤ)).app X
  have e : ι.mapTriangle.obj U ≅ T := Triangle.isoMk _ _
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.comp_id (Q.map S.f)).trans (Category.id_comp _).symm)
    ((Category.comp_id (Q.map S.g)).trans (Category.id_comp _).symm)
    (by
      let G := shiftFunctor (DerivedCategory A) (1 : ℤ)
      let h : Q.obj S.X₃ ⟶ G.obj (ι.obj X) := T.mor₃
      change ((h ≫ d.inv) ≫ d.hom) ≫ G.map (𝟙 _) = 𝟙 _ ≫ h
      calc
        _ = ((h ≫ d.inv) ≫ d.hom) ≫ 𝟙 _ :=
          congrArg (((h ≫ d.inv) ≫ d.hom) ≫ ·) (G.map_id _)
        _ = (h ≫ d.inv) ≫ d.hom := Category.comp_id _
        _ = h ≫ (d.inv ≫ d.hom) := Category.assoc _ _ _
        _ = h := (congrArg (h ≫ ·) d.inv_hom_id).trans (Category.comp_id _)
        _ = _ := (Category.id_comp _).symm)
  change ι.mapTriangle.obj U ∈ distTriang (DerivedCategory A)
  exact isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hS) _ e

private theorem isZero_ofCochainComplex (K : CochainComplex A ℤ) (b : ℤ)
    [K.IsStrictlyLE b] (h : IsZero K) : IsZero (ofCochainComplex K b) := by
  let e := ObjectProperty.fullyFaithfulι (DerivedCategory.TStructure.t
    (C := A)).minus
  apply (IsZero.iff_id_eq_zero _).2
  apply e.map_injective
  exact (IsZero.iff_id_eq_zero _).1 (DerivedCategory.Q.map_isZero h)

private theorem isIso_homologyMap_mor₁_of_isLE_obj₃
    {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
    (T : Triangle (DerivedCategory B)) (hT : T ∈ distTriang (DerivedCategory B))
    (a q : ℤ) [T.obj₃.IsLE a] (hq : a < q - 1) :
    IsIso ((DerivedCategory.homologyFunctor B q).map T.mor₁) := by
  have : Epi ((DerivedCategory.homologyFunctor B q).map T.mor₁) := by
    rw [DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT q]
    exact (DerivedCategory.isZero_of_isLE T.obj₃ a q (by omega)).eq_zero_of_tgt _
  have : Mono ((DerivedCategory.homologyFunctor B q).map T.mor₁) := by
    rw [DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT (q - 1) q (by omega)]
    exact (DerivedCategory.isZero_of_isLE T.obj₃ a (q - 1) hq).eq_zero_of_src _
  exact isIso_of_mono_of_epi _

variable {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
  {F G : Minus A ⥤ DerivedCategory B}
  (η : F ⟶ G)

/-- Invertibility at all shifts of the given bounded-above object. -/
abbrev isIsoAppAtShifts (K : Minus A) : Prop :=
  ∀ j : ℤ, IsIso (η.app (K⟦j⟧))

private theorem isoLocus_single
    (M : A) (n : ℤ)
    (h : ∀ j : ℤ,
      IsIso (η.app (ofCochainComplex ((CochainComplex.singleFunctor A j).obj M) j))) :
    isIsoAppAtShifts η
      (ofCochainComplex ((CochainComplex.singleFunctor A n).obj M) n) := by
  intro j
  let X := ofCochainComplex ((CochainComplex.singleFunctor A n).obj M) n
  let Y := ofCochainComplex ((CochainComplex.singleFunctor A (n - j)).obj M) (n - j)
  let ι : Minus A ⥤ DerivedCategory A := Minus.ι
  let e₁ := (DerivedCategory.singleFunctorIsoCompQ A n).app M
  let e₂ := (DerivedCategory.singleFunctorIsoCompQ A (n - j)).app M
  let e₃ := ((DerivedCategory.singleFunctors A).shiftIso j (n - j) n (by omega)).app M
  let e : ι.obj (X⟦j⟧) ≅ ι.obj Y :=
    (ι.commShiftIso j).app X ≪≫ (shiftFunctor _ j).mapIso e₁.symm ≪≫ e₃ ≪≫ e₂
  let hι := ObjectProperty.fullyFaithfulι (DerivedCategory.TStructure.t (C := A)).minus
  let d := hι.preimageIso e
  exact (η.isIso_app_iff_of_iso d).2 (h (n - j))

variable [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]

/-- The finite brutal truncation in the bounded-above derived category
lies in the invertibility locus when all the terms do. -/
theorem isoLocusAtShifts_ofCochainComplex_stupidTruncGE
    (K : CochainComplex A ℤ) (b : ℤ) [K.IsStrictlyLE b]
    (h : ∀ p n : ℤ,
      IsIso (η.app (ofCochainComplex ((CochainComplex.singleFunctor A n).obj (K.X p)) n)))
    (a : ℤ) :
    letI := Stacks.HomotopyDevissage.isStrictlyLE_stupidTruncGE K a b
    isIsoAppAtShifts η (ofCochainComplex (K.stupidTrunc (embeddingUpIntGE a)) b) := by
  let T (i : ℤ) := K.stupidTrunc (embeddingUpIntGE i)
  let (i : ℤ) : CochainComplex.IsStrictlyLE (T i) b :=
    Stacks.HomotopyDevissage.isStrictlyLE_stupidTruncGE K i b
  let D (i : ℤ) := ofCochainComplex (T i) b
  have htop (t : ℤ) (ht : b < t) : isIsoAppAtShifts η (D t) := by
    intro j
    have hz : IsZero (T t) := Stacks.HomotopyDevissage.isZero_of_isZero_X (T t) (fun i => by
      by_cases hi : b < i
      · exact CochainComplex.isZero_of_isStrictlyLE (T t) b i hi
      · exact CochainComplex.isZero_of_isStrictlyGE _ t i (by omega))
    have hZ := (shiftFunctor (Minus A) j).map_isZero (isZero_ofCochainComplex _ b hz)
    exact (F.map_isZero hZ).isIso (G.map_isZero hZ) _
  have hstep (m : ℕ) : isIsoAppAtShifts η (D (b + 1 - (m : ℤ))) := by
    induction m with
    | zero => exact htop _ (by omega)
    | succ m hm =>
      let p : ℤ := b + 1 - ((m + 1 : ℕ) : ℤ)
      let S := stupidTruncGEShortComplex K p
      let hS := stupidTruncGEShortComplex_shortExact K p
      let : S.X₁.IsStrictlyLE b := inferInstanceAs (CochainComplex.IsStrictlyLE (T (p + 1)) b)
      let : S.X₂.IsStrictlyLE b := inferInstanceAs (CochainComplex.IsStrictlyLE (T p) b)
      let : S.X₃.IsStrictlyLE p :=
        inferInstanceAs (((CochainComplex.singleFunctor A p).obj (K.X p)).IsStrictlyLE p)
      let U := triangleOfSES S hS b b p
      have hp : b + 1 - (m : ℤ) = p + 1 := by dsimp [p]; omega
      have h₁ : isIsoAppAtShifts η (D (p + 1)) := hp ▸ hm
      have h₃ : isIsoAppAtShifts η (U.obj₃) := isoLocus_single η (K.X p) p (h p)
      exact Stacks.CategoryTheory.ComponentwiseInvertibility.isIso_app_middle_of_all_shifts
        F G η U (triangleOfSES_distinguished S hS b b p) h₁ h₃
  by_cases ha : b < a
  · exact htop a ha
  · have ha' : b + 1 - (((b + 1 - a).toNat : ℕ) : ℤ) = a := by omega
    exact ha' ▸ hstep (b + 1 - a).toNat

/-- A natural transformation on the native bounded-above derived
category is invertible on a strictly bounded-above complex when it is
invertible on its terms and both functors have the required upper
bounds on the actual brutal quotients. -/
theorem isIso_app_ofCochainComplex_of_isIso_app_singleFunctor_X
    (K : CochainComplex A ℤ) (b c : ℤ) [K.IsStrictlyLE b]
    (h : ∀ p n : ℤ,
      IsIso (η.app (ofCochainComplex ((CochainComplex.singleFunctor A n).obj (K.X p)) n)))
    (hF : ∀ a : ℤ,
      (F.obj (ofCochainComplex (K.stupidTrunc (embeddingUpIntLE a)) a)).IsLE (a + c))
    (hG : ∀ a : ℤ,
      (G.obj (ofCochainComplex (K.stupidTrunc (embeddingUpIntLE a)) a)).IsLE (a + c)) :
    IsIso (η.app (ofCochainComplex K b)) := by
  apply (DerivedCategory.isIso_iff _ _).2
  intro q
  let a := q - c - 1
  let L := K.stupidTrunc (embeddingUpIntGE a)
  let : CochainComplex.IsStrictlyLE L b := Stacks.HomotopyDevissage.isStrictlyLE_stupidTruncGE K a b
  let X := ofCochainComplex L b
  let Y := ofCochainComplex K b
  let S := stupidTruncGELEShortComplex K a
  let hS := stupidTruncGELEShortComplex_shortExact K a
  let : S.X₁.IsStrictlyLE b := inferInstanceAs (CochainComplex.IsStrictlyLE L b)
  let : S.X₂.IsStrictlyLE b := inferInstanceAs (K.IsStrictlyLE b)
  let : S.X₃.IsStrictlyLE (a - 1) :=
    inferInstanceAs (CochainComplex.IsStrictlyLE (K.stupidTrunc (embeddingUpIntLE (a - 1))) (a - 1))
  let T := triangleOfSES S hS b b (a - 1)
  have hT : T ∈ distTriang (Minus A) := triangleOfSES_distinguished S hS b b (a - 1)
  let f : X ⟶ Y := T.mor₁
  let H := DerivedCategory.homologyFunctor B q
  let : (F.mapTriangle.obj T).obj₃.IsLE (a - 1 + c) := hF (a - 1)
  let : (G.mapTriangle.obj T).obj₃.IsLE (a - 1 + c) := hG (a - 1)
  have ha : a - 1 + c < q - 1 := by dsimp [a]; omega
  let : IsIso (H.map (F.map f)) :=
    isIso_homologyMap_mor₁_of_isLE_obj₃ _ (F.map_distinguished T hT) _ q ha
  let : IsIso (H.map (G.map f)) :=
    isIso_homologyMap_mor₁_of_isLE_obj₃ _ (G.map_distinguished T hT) _ q ha
  let : IsIso (η.app X) :=
    (η.isIso_app_iff_of_iso ((shiftFunctorZero (Minus A) ℤ).app X)).1
      (isoLocusAtShifts_ofCochainComplex_stupidTruncGE η K b h a 0)
  have he : H.map (F.map f) ≫ H.map (η.app Y) = H.map (η.app X) ≫ H.map (G.map f) :=
    (H.map_comp _ _).symm.trans ((congrArg H.map (η.naturality f)).trans (H.map_comp _ _))
  let : IsIso (H.map (F.map f) ≫ H.map (η.app Y)) := he.symm ▸ inferInstance
  exact IsIso.of_isIso_comp_left (H.map (F.map f)) _

end DerivedCategory.Minus
