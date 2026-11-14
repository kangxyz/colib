/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.GodementTotalFunctor
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.GodementTermExactness
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.TotalComplexExactness
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules

/-! # Exactness of the native Godement totalization

Short exact sequences of native bounded below complexes give short exact sequences of
Godement bicomplexes degree by degree, hence also of their diagonal coproduct totals.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.GodementResolution
open HomologicalComplex RingedSpaceModuleAdjunction

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme.Modules.BoundedBelowPerfect

universe u

variable {X : Scheme.{u}}

local notation "c" => ComplexShape.up ℤ
local notation "C" => CochainComplex X.Modules ℤ

/-- The actual map of Godement double complexes induced by a cochain map. -/
def godementDoubleMap {K L : C} (f : K ⟶ L) :
    godementDoubleComplex X.toRingedSpace K ⟶ godementDoubleComplex X.toRingedSpace L :=
  extendMap (godementRowsMap f) ComplexShape.embeddingUpNat

/-- The short complex obtained by applying the native Godement bicomplex construction. -/
def godementDoubleShortComplex (S : ShortComplex C) :
    ShortComplex (HomologicalComplex₂ X.Modules c c) :=
  ShortComplex.mk (godementDoubleMap S.f) (godementDoubleMap S.g) (by
    dsimp [godementDoubleMap]
    rw [← extendMap_comp]
    have h : godementRowsMap S.f ≫ godementRowsMap S.g = 0 := by
      apply HomologicalComplex.hom_ext
      intro i
      apply HomologicalComplex.hom_ext
      intro j
      have hz : S.f.f j ≫ S.g.f j = 0 := by
        have h := congrArg (fun f : S.X₁ ⟶ S.X₃ => f.f j) S.zero
        simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using h
      change ((godementComplex X.toRingedSpace).map (S.f.f j)).f i ≫
        ((godementComplex X.toRingedSpace).map (S.g.f j)).f i = 0
      rw [← HomologicalComplex.comp_f, ← Functor.map_comp, hz, Functor.map_zero,
        HomologicalComplex.zero_f]
    rw [h, extendMap_zero])

/-- Every bidegree of the Godement double complex preserves short exact sequences. -/
theorem godementDouble_shortExact {S : ShortComplex C} (hS : S.ShortExact) (p q : ℤ) :
    (((godementDoubleShortComplex S).map (HomologicalComplex.eval _ c p)).map
      (HomologicalComplex.eval _ c q)).ShortExact := by
  let T := godementDoubleShortComplex S
  change ((T.map (HomologicalComplex.eval _ c p)).map (HomologicalComplex.eval _ c q)).ShortExact
  by_cases hp : 0 ≤ p
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    let F : X.Modules ⥤ X.Modules :=
      godementComplex X.toRingedSpace ⋙ HomologicalComplex.eval _ (ComplexShape.up ℕ) k
    let : F.PreservesZeroMorphisms := inferInstanceAs
      ((godementComplex X.toRingedSpace ⋙
        HomologicalComplex.eval _ (ComplexShape.up ℕ) k).PreservesZeroMorphisms)
    let R := (S.map (HomologicalComplex.eval _ c q)).map F
    have hR : R.ShortExact :=
      godementTerm_shortExact (X := X.toRingedSpace)
        (hS.map_of_exact (HomologicalComplex.eval X.Modules c q)) k
    let e (K : C) :=
      (godementRows X.toRingedSpace K).extendXIso ComplexShape.embeddingUpNat
        (i := k) (i' := (k : ℤ)) rfl
    let E (K : C) := (HomologicalComplex.eval X.Modules c q).mapIso (e K)
    let i : ((T.map (HomologicalComplex.eval _ c (k : ℤ))).map
        (HomologicalComplex.eval _ c q)) ≅ R :=
      ShortComplex.isoMk (E S.X₁) (E S.X₂) (E S.X₃) (Eq.symm (by
        change ((godementDoubleMap S.f).f (k : ℤ)).f q ≫ (e S.X₂).hom.f q =
          (e S.X₁).hom.f q ≫ ((godementComplex X.toRingedSpace).map (S.f.f q)).f k
        rw [godementDoubleMap, extendMap_f _ _
          (show ComplexShape.embeddingUpNat.f k = (k : ℤ) from rfl)]
        simp [e, godementRowsMap, HomologicalComplex.comp_f])) (Eq.symm (by
        change ((godementDoubleMap S.g).f (k : ℤ)).f q ≫ (e S.X₃).hom.f q =
          (e S.X₂).hom.f q ≫ ((godementComplex X.toRingedSpace).map (S.g.f q)).f k
        rw [godementDoubleMap, extendMap_f _ _
          (show ComplexShape.embeddingUpNat.f k = (k : ℤ) from rfl)]
        simp [e, godementRowsMap, HomologicalComplex.comp_f]))
    exact (ShortComplex.shortExact_iff_of_iso i).mpr hR
  · let R := (T.map (HomologicalComplex.eval _ c p)).map (HomologicalComplex.eval _ c q)
    have hz (K : C) : IsZero (((godementDoubleComplex X.toRingedSpace K).X p).X q) :=
      isZero_liftFunctorToComplexExtend_X_X_of_neg (godementComplex X.toRingedSpace)
        (fun _ => inferInstance) K p q (by omega)
    have h₁ : IsZero R.X₁ := hz S.X₁
    have h₂ : IsZero R.X₂ := hz S.X₂
    have h₃ : IsZero R.X₃ := hz S.X₃
    have : Mono R.f := ⟨fun _ _ _ => h₁.eq_of_tgt _ _⟩
    have : Epi R.g := ⟨fun _ _ _ => h₃.eq_of_src _ _⟩
    exact { exact := ShortComplex.exact_of_isZero_X₂ _ h₂ }

instance godementTotal_additive (X : Scheme.{u}) : (godementTotal X).Additive where
  map_add {K L f g} := by
    have h : godementRowsMap (f.hom + g.hom) = godementRowsMap f.hom + godementRowsMap g.hom := by
      apply HomologicalComplex.hom_ext
      intro p
      apply HomologicalComplex.hom_ext
      intro q
      change ((godementComplex X.toRingedSpace).map (f.hom.f q + g.hom.f q)).f p =
        ((godementComplex X.toRingedSpace).map (f.hom.f q)).f p +
          ((godementComplex X.toRingedSpace).map (g.hom.f q)).f p
      let F := godementComplex X.toRingedSpace ⋙ HomologicalComplex.eval _ (ComplexShape.up ℕ) p
      let : F.Additive := godementTerm_additive X.toRingedSpace p
      exact F.map_add
    apply ObjectProperty.hom_ext
    change HomologicalComplex₂.total.map
        (extendMap (godementRowsMap (f.hom + g.hom)) ComplexShape.embeddingUpNat) c = _
    rw [h]
    let E := ComplexShape.embeddingUpNat.extendFunctor (CochainComplex X.Modules ℤ)
    let T := HomologicalComplex₂.totalFunctor X.Modules c c c
    exact (congrArg T.map
      (E.map_add (f := godementRowsMap f.hom) (g := godementRowsMap g.hom))).trans
      T.map_add

/-- Actual bounded below Godement totalization preserves short exact sequences. -/
theorem godementTotal_shortExact {S : ShortComplex (Obj X)}
    (hS : (S.map (objects X).ι).ShortExact) :
    ((S.map (godementTotal X)).map (objects X).ι).ShortExact := by
  let T := S.map (objects X).ι
  exact HomologicalComplex₂.total_shortExact (S := godementDoubleShortComplex T)
    (godementDouble_shortExact hS)

end AlgebraicGeometry.Scheme.Modules.BoundedBelowPerfect
