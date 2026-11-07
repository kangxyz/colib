/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.GrothendieckComparison.IdentityCofiberSuffix

/-!
# Literal cofiber rows, full affine triangle tracks and identity suffixes

These focused assertions use independent object and morphism universes. Zero
morphisms are assumed only in the section that uses the displayed row maps.
The tests do not import the optional weak-row comparison or cofiber-prism cube.
-/

@[expose] public noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.QuotientRows SSet
open scoped Simplicial Topology unitInterval

namespace ColibTest.WaldhausenLiteralCofiberTriangle

section Triangle

variable {n : ℕ} {x y : |(Δ[n] : SSet.{u})|} (p q : Path x y)

example : p.Homotopy q := realizationStdSimplexPathHomotopy p q

example (r t : unitInterval) :
    realizationStdSimplexPathHomotopy p q (r, t) =
      (SimplexCategory.toTopHomeo (SimplexCategory.mk n)).symm
        (Convexity.StdSimplex.pathHomotopy
          (p.map (SimplexCategory.toTopHomeo (SimplexCategory.mk n)).continuous)
          (q.map (SimplexCategory.toTopHomeo (SimplexCategory.mk n)).continuous) (r, t)) := rfl

example (r t : unitInterval) (j : Fin (n + 1)) :
    ((SimplexCategory.toTopHomeo (SimplexCategory.mk n))
      (realizationStdSimplexPathHomotopy p q (r, t))).weights j =
        (1 - (r : ℝ)) * ((SimplexCategory.toTopHomeo (SimplexCategory.mk n)) (p t)).weights j +
          (r : ℝ) * ((SimplexCategory.toTopHomeo (SimplexCategory.mk n)) (q t)).weights j := by
  let e := SimplexCategory.toTopHomeo (SimplexCategory.mk n)
  change (e (e.symm (Convexity.StdSimplex.pathHomotopy
    (p.map e.continuous) (q.map e.continuous) (r, t)))).weights j = _
  rw [e.apply_symm_apply]
  exact Convexity.StdSimplex.pathHomotopy_apply _ _ _ _ _

end Triangle

section Objects

variable {C : Type u} [Category.{v} C] (W : Structure C) (A B Q : C)

example : cofiberTwoObject W (A := A) (B := B) (Q := Q) (interval 0 0 (by decide)) =
    W.zero := rfl

example : cofiberTwoObject W (A := A) (B := B) (Q := Q) (interval 0 1 (by decide)) =
    A := rfl

example : cofiberTwoObject W (A := A) (B := B) (Q := Q) (interval 0 2 (by decide)) =
    B := rfl

example : cofiberTwoObject W (A := A) (B := B) (Q := Q) (interval 1 1 (by decide)) =
    W.zero := rfl

example : cofiberTwoObject W (A := A) (B := B) (Q := Q) (interval 1 2 (by decide)) =
    Q := rfl

example : cofiberTwoObject W (A := A) (B := B) (Q := Q) (interval 2 2 (by decide)) =
    W.zero := rfl

example : cofiberFaceObject (A := A) (B := B) (Q := Q) 0 = Q := rfl

example : cofiberFaceObject (A := A) (B := B) (Q := Q) 1 = B := rfl

example : cofiberFaceObject (A := A) (B := B) (Q := Q) 2 = A := rfl

end Objects

section Cofiber

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  (W : Structure C) {A B Q : C} (i : A ⟶ B) (q : B ⟶ Q)
  (hi : W.cof i) (hQ : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q))

-- The transports are the concrete object equalities above, retaining the literal row arrows.
example : cofiberTwoMap W i q
    (homOfLE (show interval 0 1 (by decide) ≤ interval 0 2 (by decide) from by decide)) =
      eqToHom (show cofiberTwoObject W (A := A) (B := B) (Q := Q)
        (interval 0 1 (by decide)) = A from rfl) ≫
        i ≫ eqToHom (show B = cofiberTwoObject W (A := A) (B := B) (Q := Q)
          (interval 0 2 (by decide)) from rfl) := by
  simp [cofiberTwoMap, interval]

example : cofiberTwoMap W i q
    (homOfLE (show interval 0 2 (by decide) ≤ interval 1 2 (by decide) from by decide)) =
      eqToHom (show cofiberTwoObject W (A := A) (B := B) (Q := Q)
        (interval 0 2 (by decide)) = B from rfl) ≫
        q ≫ eqToHom (show Q = cofiberTwoObject W (A := A) (B := B) (Q := Q)
          (interval 1 2 (by decide)) from rfl) := by
  simp [cofiberTwoMap, interval]

example : cofiberTwoMap W i q
    (homOfLE (show interval 0 1 (by decide) ≤ interval 1 2 (by decide) from by decide)) =
      eqToHom (show cofiberTwoObject W (A := A) (B := B) (Q := Q)
        (interval 0 1 (by decide)) = A from rfl) ≫
        (0 : A ⟶ Q) ≫ eqToHom (show Q = cofiberTwoObject W (A := A) (B := B) (Q := Q)
          (interval 1 2 (by decide)) from rfl) := by
  simp [cofiberTwoMap, interval]

example : i ≫ q = 0 := cofiberTwo_comp_eq_zero W i q hQ

example : Obj W ⦋2⦌ := cofiberTwoRow W i q hi hQ

example (k : Fin 3) :
    indexMap (SimplexCategory.δ k) ⋙
        cofiberTwoDiagram W i q (cofiberTwo_comp_eq_zero W i q hQ) =
      oneDiagram W (cofiberFaceObject (A := A) (B := B) (Q := Q) k) :=
  cofiberTwoDiagram_face W i q _ k

example : (sSet W.cof W.weq).δ 0 (W.cofiberObjectSimplex i q hi hQ) =
    W.kZeroObjectSimplex Q := W.cofiberObjectSimplex_face i q hi hQ 0

example : (sSet W.cof W.weq).δ 1 (W.cofiberObjectSimplex i q hi hQ) =
    W.kZeroObjectSimplex B := W.cofiberObjectSimplex_face i q hi hQ 1

example : (sSet W.cof W.weq).δ 2 (W.cofiberObjectSimplex i q hi hQ) =
    W.kZeroObjectSimplex A := W.cofiberObjectSimplex_face i q hi hQ 2

example : (W.cofiberObjectCompStruct i q hi hQ).simplex =
    W.cofiberObjectSimplex i q hi hQ := rfl

example (r t : unitInterval) :
    W.cofiberObjectLoopTrack i q hi hQ (r, t) =
      SSet.toTop.map (SSet.yonedaEquiv.symm (W.cofiberObjectSimplex i q hi hQ))
        (realizationStdSimplexPathHomotopy
          ((realizationEdgePath (simplexEdge.{max u v} 2 0 1 (by decide))).trans
            (realizationEdgePath (simplexEdge.{max u v} 2 1 2 (by decide))))
          (realizationEdgePath (simplexEdge.{max u v} 2 0 2 (by decide))) (r, t)) :=
  realizationEdgeCompositionHomotopy_apply (W.cofiberObjectCompStruct i q hi hQ) r t

example (A : C) :
    IsPushout (𝟙 A) (0 : A ⟶ W.zero) (0 : A ⟶ W.zero) (0 : W.zero ⟶ W.zero) :=
  cofiberTwo_identity_square W

example (A : C) :
    Path ((W.kZeroObjectLoop A).trans (Path.refl W.kBasepoint)) (W.kZeroObjectLoop A) :=
  W.identityCofiberSuffixPath A

example (A : C) (s t : unitInterval) :
    W.identityCofiberSuffixPath A s t =
      W.cofiberObjectLoopTrack (𝟙 A) (0 : A ⟶ W.zero) (W.cof.id_mem A)
        (cofiberTwo_identity_square W) (s, t) := W.identityCofiberSuffixPath_apply A s t

example (A : C) (t : unitInterval) :
    W.identityCofiberSuffixPath A 0 t =
      ((W.kZeroObjectLoop A).trans (Path.refl W.kBasepoint)) t :=
  congrArg (fun p ↦ p t) (W.identityCofiberSuffixPath A).source

example (A : C) (t : unitInterval) :
    W.identityCofiberSuffixPath A 1 t = W.kZeroObjectLoop A t :=
  congrArg (fun p ↦ p t) (W.identityCofiberSuffixPath A).target

end Cofiber

end ColibTest.WaldhausenLiteralCofiberTriangle
