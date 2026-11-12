/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicTopology.DoldKan.NormalizedRepresentatives
public import Mathlib.Algebra.Homology.Single

/-!
# Vanishing of a Moore term with a monic positive face

Each normalized simplex is killed by every positive face. A monic positive
face therefore forces the whole normalized Moore term to vanish.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicTopology.NormalizedMooreComplex

variable (X : SimplicialObject AddCommGrpCat.{u})

open AlgebraicTopology.DoldKan
open scoped Simplicial

/-- A monic positive face kills the entire normalized term in that degree. -/
theorem isZero_normalizedMooreTerm_of_mono_face (n : ℕ) (i : Fin (n + 1))
    [Mono (X.δ i.succ)] :
    IsZero (((normalizedMooreComplex AddCommGrpCat).obj X).X (n + 1)) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply AddCommGrpCat.ext
  intro x
  change x = 0
  apply inclusion_injective X (n + 1)
  rw [map_zero]
  apply (AddCommGrpCat.mono_iff_injective (X.δ i.succ)).1 inferInstance
  rw [map_zero]
  exact isNormalized_inclusion X (n + 1) x i

/-- If a monic positive face exists in every positive degree, the map from
a coefficient group into the alternating complex is a quasi-isomorphism
as soon as its degree-zero component is an isomorphism. -/
theorem quasiIso_fromSingle_of_mono_faces (A : AddCommGrpCat.{u})
    (f : (ChainComplex.single₀ AddCommGrpCat).obj A ⟶
      (alternatingFaceMapComplex AddCommGrpCat).obj X)
    (h : ∀ n : ℕ, ∃ i : Fin (n + 1), Mono (X.δ i.succ))
    [IsIso (f.f 0)] : QuasiIso f := by
  let e := homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y := X)
  have h₀ : e.inv.f 0 ≫ e.hom.f 0 = 𝟙 _ := by
    change (PInftyToNormalizedMooreComplex X).f 0 ≫ (inclusionOfMooreComplexMap X).f 0 = _
    have hp := congrArg (fun g => g.f 0)
      (PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap X)
    exact hp.trans PInfty_f_0
  have h₁ : e.hom.f 0 ≫ e.inv.f 0 = 𝟙 _ := by
    exact congrArg (fun g => g.f 0) (splitMonoInclusionOfMooreComplexMap X).id
  let : IsIso (e.inv.f 0) := ⟨⟨e.hom.f 0, h₀, h₁⟩⟩
  let g := f ≫ e.inv
  let (n : ℕ) : IsIso (g.f n) := by
    cases n with
    | zero =>
        change IsIso (f.f 0 ≫ e.inv.f 0)
        infer_instance
    | succ n =>
        obtain ⟨i, hi⟩ := h n
        let : Mono (X.δ i.succ) := hi
        exact (HomologicalComplex.isZero_single_obj_X (.down ℕ) 0 A (n + 1) (by omega)).isIso
          (isZero_normalizedMooreTerm_of_mono_face X n i) _
  let : IsIso g := HomologicalComplex.Hom.isIso_of_components g
  let : QuasiIso (f ≫ e.inv) := quasiIso_of_isIso g
  let : QuasiIso e.inv := e.quasiIso_inv
  exact quasiIso_of_comp_right f e.inv

end AlgebraicTopology.NormalizedMooreComplex
