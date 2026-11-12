/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.ShortComplex.AbRepresentative
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence

/-!
# Cycle representatives in a normalized Moore complex

The inclusion of the native normalized Moore complex identifies its cycles
with simplices killed by every face. A boundary is the zeroth face of a
simplex killed by the other faces. These representatives give an elementwise
criterion for the alternating face map complex to induce a homology isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Subobject Opposite
open scoped Simplicial

universe u

namespace AlgebraicTopology.NormalizedMooreComplex

open _root_.AlgebraicTopology.DoldKan

variable (X : SimplicialObject AddCommGrpCat.{u})

local notation "N(" Z ")" => Functor.obj (normalizedMooreComplex AddCommGrpCat) Z
local notation "A(" Z ")" => Functor.obj (alternatingFaceMapComplex AddCommGrpCat) Z
local notation "ι(" Z "," n ")" => HomologicalComplex.Hom.f (inclusionOfMooreComplexMap Z) n

/-- A normalized simplex is killed by all the positive faces. -/
def IsNormalized : ∀ n : ℕ, X.obj (op ⦋n⦌) → Prop
  | 0, _ => True
  | n + 1, x => ∀ i : Fin (n + 1), X.δ i.succ x = 0

/-- A cycle in the normalized complex is killed by all the faces. -/
def IsCycle : ∀ n : ℕ, X.obj (op ⦋n⦌) → Prop
  | 0, _ => True
  | n + 1, x => ∀ i : Fin (n + 2), X.δ i x = 0

/-- A normalized boundary is the zeroth face of a normalized simplex. -/
def IsBoundary (n : ℕ) (x : X.obj (op ⦋n⦌)) : Prop :=
  ∃ y : X.obj (op ⦋n + 1⦌), IsNormalized X (n + 1) y ∧ X.δ (0 : Fin (n + 2)) y = x

/-- The Moore inclusion is injective in each degree. -/
theorem inclusion_injective (n : ℕ) : Function.Injective (ι(X, n)) := by
  rw [inclusionOfMooreComplexMap_f]
  exact (AddCommGrpCat.mono_iff_injective _).1 (Subobject.arrow_mono (objX X n))

/-- The image of an element of the native Moore term is normalized. -/
theorem isNormalized_inclusion (n : ℕ) (x : (N(X)).X n) :
    IsNormalized X n (ι(X, n) x) := by
  rcases n with _ | n
  · trivial
  · intro i
    have h := HigherFacesVanish.inclusionOfMooreComplexMap (X := X) n i
      (Nat.le_add_left (n + 1) i.val)
    exact ConcreteCategory.congr_hom h x

/-- Every normalized simplex belongs to the image of the native Moore term. -/
theorem exists_inclusion_eq_of_isNormalized (n : ℕ) (x : X.obj (op ⦋n⦌))
    (hx : IsNormalized X n x) : ∃ z : (N(X)).X n, ι(X, n) z = x := by
  let a : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ X.obj (op ⦋n⦌) :=
    AddCommGrpCat.ofHom (uliftZMultiplesHom _ x)
  have ha : (objX X n).Factors a := by
    rcases n with _ | n
    · exact top_factors _
    · rw [objX_add_one, finset_inf_factors]
      intro i _
      apply kernelSubobject_factors
      ext z
      change X.δ i.succ (z.down • x) = 0
      rw [map_zsmul, hx i, zsmul_zero]
  refine ⟨factorThru _ a ha (ULift.up 1), ?_⟩
  rw [inclusionOfMooreComplexMap_f]
  have h := ConcreteCategory.congr_hom (factorThru_arrow _ a ha) (ULift.up (1 : ℤ))
  exact h.trans (one_zsmul x)

private theorem inclusion_d (n : ℕ) (x : (N(X)).X (n + 1)) :
    ι(X, n) ((N(X)).d (n + 1) n x) = X.δ (0 : Fin (n + 2)) (ι(X, n + 1) x) := by
  have h : ι(X, n + 1) ≫ (A(X)).d (n + 1) n = ι(X, n + 1) ≫ X.δ (0 : Fin (n + 2)) := by
    simp only [alternatingFaceMapComplex, AlternatingFaceMapComplex.obj, ChainComplex.of_d,
      AlternatingFaceMapComplex.objD]
    rw [Preadditive.comp_sum, Fin.sum_univ_succ]
    have hz : (∑ i : Fin (n + 1),
        ι(X, n + 1) ≫ ((-1 : ℤ) ^ (i.succ : ℕ) • X.δ i.succ)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [Preadditive.comp_zsmul,
        HigherFacesVanish.inclusionOfMooreComplexMap (X := X) n i (Nat.le_add_left _ _),
        smul_zero]
    simp only [hz, add_zero, Fin.val_zero, pow_zero, one_zsmul]
  exact ConcreteCategory.congr_hom
    (((inclusionOfMooreComplexMap X).comm (n + 1) n).symm.trans h) x

/-- The cycle condition in the native Moore short complex is vanishing on all faces. -/
theorem isCycle_inclusion_iff (n : ℕ) (x : (N(X)).X n) :
    IsCycle X n (ι(X, n) x) ↔ ((N(X)).sc n).g x = 0 := by
  rcases n with _ | n
  · change True ↔ (N(X)).d 0 ((ComplexShape.down ℕ).next 0) x = 0
    rw [(N(X)).shape _ _ (by simp)]
    exact iff_of_true trivial rfl
  · change (∀ i : Fin (n + 2), X.δ i (ι(X, n + 1) x) = 0) ↔
      (N(X)).d (n + 1) ((ComplexShape.down ℕ).next (n + 1)) x = 0
    rw [(ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl)]
    constructor
    · intro h
      apply inclusion_injective X n
      rw [map_zero, inclusion_d]
      exact h 0
    · intro h i
      refine Fin.cases ?_ (fun j => isNormalized_inclusion X (n + 1) x j) i
      rw [← inclusion_d, h, map_zero]

/-- A boundary in the Moore short complex has the prescribed literal zeroth face. -/
theorem isBoundary_inclusion_iff (n : ℕ) (x : (N(X)).X n) :
    IsBoundary X n (ι(X, n) x) ↔ ∃ y : ((N(X)).sc n).X₁, ((N(X)).sc n).f y = x := by
  change IsBoundary X n (ι(X, n) x) ↔ ∃ y : (N(X)).X ((ComplexShape.down ℕ).prev n),
    (N(X)).d ((ComplexShape.down ℕ).prev n) n y = x
  rw [(ComplexShape.down ℕ).prev_eq' (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl)]
  constructor
  · rintro ⟨y, hy, hface⟩
    obtain ⟨z, rfl⟩ := exists_inclusion_eq_of_isNormalized X (n + 1) y hy
    exact ⟨z, inclusion_injective X n ((inclusion_d X n z).trans hface)⟩
  · rintro ⟨y, rfl⟩
    exact ⟨ι(X, n + 1) y, isNormalized_inclusion X (n + 1) y, (inclusion_d X n y).symm⟩

private theorem retraction_inclusion (n : ℕ) (x : (N(X)).X n) :
    (PInftyToNormalizedMooreComplex X).f n (ι(X, n) x) = x := by
  have h := (splitMonoInclusionOfMooreComplexMap X).id
  change inclusionOfMooreComplexMap X ≫ PInftyToNormalizedMooreComplex X = 𝟙 _ at h
  exact ConcreteCategory.congr_hom (congrArg (fun f => f.f n) h) x

/-- An alternating boundary which is normalized is a normalized boundary.
Use the canonical Moore retraction on its original bounding chain. -/
theorem isBoundary_of_alternatingBoundary (n : ℕ) (x : X.obj (op ⦋n⦌))
    (hx : IsNormalized X n x)
    (y : (A(X)).X (n + 1)) (hy : (A(X)).d (n + 1) n y = x) :
    IsBoundary X n x := by
  obtain ⟨z, rfl⟩ := exists_inclusion_eq_of_isNormalized X n x hx
  let r := PInftyToNormalizedMooreComplex X
  have h := ConcreteCategory.congr_hom (r.comm (n + 1) n) y
  change (N(X)).d (n + 1) n (r.f (n + 1) y) =
    r.f n ((A(X)).d (n + 1) n y) at h
  rw [hy, retraction_inclusion X n z] at h
  exact ⟨ι(X, n + 1) (r.f (n + 1) y), isNormalized_inclusion X (n + 1) _,
    (inclusion_d X n _).symm.trans (congrArg (ι(X, n)) h)⟩

/-- A chain homotopy gives a normalized boundary between the images of a
cycle when their difference is a normalized simplex. -/
theorem isBoundary_sub_of_homotopy {K : ChainComplex AddCommGrpCat.{u} ℕ}
    {f g : K ⟶ A(X)} (H : Homotopy f g) (n : ℕ) (x : K.X n)
    (hx : (K.sc n).g x = 0) (hn : IsNormalized X n (f.f n x - g.f n x)) :
    IsBoundary X n (f.f n x - g.f n x) := by
  apply isBoundary_of_alternatingBoundary X n _ hn (H.hom n (n + 1) x)
  have h := H.comm n
  rw [dNext_eq_dFrom_fromNext, Homotopy.prevD_chainComplex] at h
  have he := ConcreteCategory.congr_hom h x
  change f.f n x = fromNext n H.hom (K.dFrom n x) +
    (A(X)).d (n + 1) n (H.hom n (n + 1) x) + g.f n x at he
  change K.dFrom n x = 0 at hx
  rw [hx, map_zero, zero_add] at he
  exact eq_sub_iff_add_eq.mpr he.symm

variable {X Y : SimplicialObject AddCommGrpCat.{u}}

private theorem inclusion_map (f : X ⟶ Y) (n : ℕ) (x : (N(X)).X n) :
    ι(Y, n) (((normalizedMooreComplex AddCommGrpCat).map f).f n x) =
      f.app (op ⦋n⦌) (ι(X, n) x) :=
  ConcreteCategory.congr_hom
    (congrArg (fun g => g.f n) ((inclusionOfMooreComplex AddCommGrpCat).naturality f)) x

/-- Reflection of normalized boundaries and surjectivity on cycles modulo
normalized boundaries imply that the actual alternating chain map is a quasi-isomorphism. -/
theorem quasiIso_alternatingFaceMapComplex_of_normalized (f : X ⟶ Y)
    (hinj : ∀ (n : ℕ) (x : X.obj (op ⦋n⦌)), IsCycle X n x →
      IsBoundary Y n (f.app (op ⦋n⦌) x) → IsBoundary X n x)
    (hsurj : ∀ (n : ℕ) (y : Y.obj (op ⦋n⦌)), IsCycle Y n y →
      ∃ x : X.obj (op ⦋n⦌), IsCycle X n x ∧ IsBoundary Y n (y - f.app (op ⦋n⦌) x)) :
    QuasiIso ((alternatingFaceMapComplex AddCommGrpCat).map f) := by
  let fn := (normalizedMooreComplex AddCommGrpCat).map f
  have hfn : QuasiIso fn := (quasiIso_iff fn).2 fun n => by
    rw [quasiIsoAt_iff, ShortComplex.quasiIso_iff]
    apply ShortComplex.isIso_homologyMap_of_ab_representatives
    · intro x hx hb
      change (N(X)).X n at x
      have hb' := (isBoundary_inclusion_iff Y n (fn.f n x)).2 hb
      exact (isBoundary_inclusion_iff X n x).1
        (hinj n (ι(X, n) x) ((isCycle_inclusion_iff X n x).2 hx)
          (inclusion_map f n x ▸ hb'))
    · intro y hy
      change (N(Y)).X n at y
      obtain ⟨x, hx, hb⟩ := hsurj n (ι(Y, n) y) ((isCycle_inclusion_iff Y n y).2 hy)
      have hnormal : IsNormalized X n x := by
        cases n
        · trivial
        · exact fun i => hx i.succ
      obtain ⟨z, rfl⟩ := exists_inclusion_eq_of_isNormalized X n x hnormal
      refine ⟨z, (isCycle_inclusion_iff X n z).1 hx,
        (isBoundary_inclusion_iff Y n (y - fn.f n z)).1 ?_⟩
      simp only [fn, map_sub, inclusion_map f]
      exact hb
  have hX : QuasiIso (inclusionOfMooreComplexMap X) :=
    (homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y := X)).quasiIso_hom
  have hY : QuasiIso (inclusionOfMooreComplexMap Y) :=
    (homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y := Y)).quasiIso_hom
  apply (quasiIso_iff_comp_left (inclusionOfMooreComplexMap X) _).1
  have h := (inclusionOfMooreComplex AddCommGrpCat).naturality f
  change fn ≫ inclusionOfMooreComplexMap Y =
    inclusionOfMooreComplexMap X ≫ (alternatingFaceMapComplex AddCommGrpCat).map f at h
  rw [← h]
  infer_instance

end AlgebraicTopology.NormalizedMooreComplex
