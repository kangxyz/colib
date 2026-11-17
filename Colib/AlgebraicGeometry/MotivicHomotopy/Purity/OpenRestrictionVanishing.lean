/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.OrientationDescent
import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.AffineBasisSubcover

/-! # Shifted Hom vanishing for relative open restrictions -/

public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits
open SmoothSite CategoryTheory.Pretriangulated

universe u v

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k]

local notation "Sm" => SmoothSite (Spec (CommRingCat.of k))

private theorem predicate_of_affine_subcover {B : Sm} {I : Type v}
    (C : I → B.left.Opens) (s : Finset I) (hc : s.sup C = ⊤)
    (Q : B.left.Opens → Prop) (hbot : Q ⊥)
    (hstep : ∀ U V, Q U → Q V → Q (U ⊓ V) → Q (U ⊔ V))
    (hchart : ∀ i : I, ∀ W : B.left.affineOpens, W.1 ≤ C i → Q W.1)
    (W : B.left.Opens) : Q W := by
  classical
  have hQ (U V : B.left.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
      IsAffineOpen (U ⊓ V) := by
    have hdiag : IsAffineHom (pullback.diagonal B.hom) := inferInstance
    exact (isAffineHom_diagonal_iff (f := B.hom)).mp hdiag ⊤
      (isAffineOpen_top (Spec (CommRingCat.of k))) U (by simp) V (by simp) hU hV
  obtain ⟨rs, hrs, hsub⟩ := Scheme.exists_finite_affine_subcover C s hc W
  let D (U : B.left.affineOpens) : B.left.Opens := U.1
  have hlocal (U : B.left.affineOpens) (hU : U ∈ rs) (V : B.left.Opens)
      (hVU : V ≤ D U) (hV : IsAffineOpen V) : Q V := by
    obtain ⟨i, _, hi⟩ := hsub U hU
    exact hchart i ⟨V, hV⟩ (hVU.trans hi)
  have hz : Q (rs.sup D) :=
    predicate_of_finset_sup_of_inf_closed Q IsAffineOpen hbot hstep hQ rs D
      (fun U _ => U.2) hlocal
  have he : rs.sup D = W := hrs
  exact he ▸ hz

variable {E : Type*} [Category E] [HasZeroObject E] [Preadditive E] [HasBinaryBiproducts E]
  [HasShift E ℤ] [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]

/-- Vanishing of shifted Hom on affine subopens of a finite cover extends to every open
by the specified binary restriction triangles. -/
theorem subsingleton_shift_openRestriction_hom_of_affine_cover
    {B : Sm} (P : B.left.Opens ⥤ E) (A : E)
    (hzero : IsZero (P.obj ⊥)) (T : ∀ U V, BinaryRestrictionTriangle P U V)
    {I : Type v} (C : I → B.left.Opens) (s : Finset I) (hc : s.sup C = ⊤)
    (hchart : ∀ i : I, ∀ W : B.left.affineOpens, W.1 ≤ C i →
      ∀ a : ℤ, 0 < a → Subsingleton ((P.obj W.1)⟦a⟧ ⟶ A))
    (W : B.left.Opens) (a : ℤ) (ha : 0 < a) :
    Subsingleton ((P.obj W)⟦a⟧ ⟶ A) := by
  let Q (U : B.left.Opens) := ∀ d : ℤ, 0 < d → Subsingleton ((P.obj U)⟦d⟧ ⟶ A)
  have hbot : Q ⊥ := by
    intro d _
    let δ := (shiftFunctor E d).map_isZero hzero
    exact ⟨fun f g => δ.eq_of_src f g⟩
  have hstep (U V : B.left.Opens) (hU : Q U) (hV : Q V) (hUV : Q (U ⊓ V)) : Q (U ⊔ V) := by
    intro d hd
    exact (T U V).shift_hom_subsingleton d
      (hU d hd) (hV d hd) (hUV (1 + d) (by omega))
  have hf : Q W := predicate_of_affine_subcover k C s hc Q hbot hstep hchart W
  exact hf a ha

end AlgebraicGeometry.MotivicHomotopy
