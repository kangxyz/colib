/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.LoopTranspose
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Fixed cyclic and reversal words in the original loop transpose

Finite looping of diagrams is functorial. The cyclic word moves the first evaluation
coordinate to the last; reversal uses this cyclic word followed by the loop of the previous
reversal. All maps use the original double-loop transpose. Their natural isomorphisms and
whole finite evaluation formulas do not involve cone permutations or a symmetric-group API.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
open Topology.LoopPrespectrum.FiniteParameterLooping
universe u v w
namespace Topology.LoopPrespectrum.FiniteLoopWords
open Topology.LoopPrespectrum.FiniteParameterLooping
variable {C : Type u} [Category.{v} C]

/-- Loop an actual map of diagrams in the same order as `loopDiagram`. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/FiniteLoopWords.lean:30"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def loopMap : ∀ (j : ℕ) {F G : C ⥤ LoopPrespectrum.{w}},
    (F ⟶ G) → (loopDiagram j F ⟶ loopDiagram j G)
  | 0, _, _, f => f
  | j + 1, _, _, f => Functor.whiskerRight (loopMap j f) parameterLoopingFunctor

/-- Finite looping retains the identity map. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/FiniteLoopWords.lean:36"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem loopMap_id (j : ℕ) (F : C ⥤ LoopPrespectrum.{w}) :
    loopMap j (𝟙 F) = 𝟙 (loopDiagram j F) := by
  induction j with
  | zero => rfl
  | succ j ih => simpa only [loopMap, ih, loopDiagram] using
      Functor.whiskerRight_id' parameterLoopingFunctor

/-- Finite looping retains composition of complete diagram maps. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/FiniteLoopWords.lean:44"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem loopMap_comp (j : ℕ) {F G H : C ⥤ LoopPrespectrum.{w}}
    (f : F ⟶ G) (g : G ⟶ H) : loopMap j (f ≫ g) = loopMap j f ≫ loopMap j g := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [loopMap, ih, Functor.whiskerRight_comp]
    rfl

/-- The actual finite-loop object assignment is an endofunctor on diagrams. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/FiniteLoopWords.lean:53"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def loopFunctor (j : ℕ) : (C ⥤ LoopPrespectrum.{w}) ⥤ (C ⥤ LoopPrespectrum.{w}) where
  obj := loopDiagram j
  map := loopMap j
  map_id := loopMap_id j
  map_comp := loopMap_comp j

/-- Evaluate exactly the prescribed finite tuple of loop coordinates. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/FiniteLoopWords.lean:60"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def evaluate : ∀ (j : ℕ) (F : C ⥤ LoopPrespectrum.{w}) (X : C) (n : ℕ),
    ((loopDiagram j F).obj X).space n → (Fin j → unitInterval) → (F.obj X).space n
  | 0, _, _, _, z, _ => z
  | j + 1, F, X, n, z, t => evaluate j F X n (Path.toContinuousMap z (t 0)) (Fin.tail t)

/-- Finite evaluation is natural in an arbitrary original map of diagrams. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/FiniteLoopWords.lean:66"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem evaluate_loopMap (j : ℕ) {F G : C ⥤ LoopPrespectrum.{w}} (f : F ⟶ G)
    (X : C) (n : ℕ) (z : ((loopDiagram j F).obj X).space n)
    (t : Fin j → unitInterval) :
    evaluate j G X n (((loopMap j f).app X).map n z) t =
      (f.app X).map n (evaluate j F X n z t) := by
  induction j with
  | zero => rfl
  | succ j ih => exact ih (Path.toContinuousMap z (t 0)) (Fin.tail t)

/-- All finite coordinate evaluations separate the original iterated loop values. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/FiniteLoopWords.lean:76"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem evaluate_ext (j : ℕ) (F : C ⥤ LoopPrespectrum.{w}) (X : C) (n : ℕ)
    {z z' : ((loopDiagram j F).obj X).space n}
    (h : ∀ t, evaluate j F X n z t = evaluate j F X n z' t) : z = z' := by
  induction j with
  | zero => exact h Fin.elim0
  | succ j ih =>
    apply Path.ext
    funext r
    apply ih
    intro t
    have hh := h (Fin.cons r t)
    simp only [evaluate, Fin.cons_zero, Fin.tail_cons] at hh
    exact hh

/-- A whole map into a finite-loop diagram is determined by all its loop evaluations. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/FiniteLoopWords.lean:91"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem evaluation_hom_ext (j : ℕ) {E F : C ⥤ LoopPrespectrum.{w}}
    {f g : E ⟶ loopDiagram j F}
    (h : ∀ X n z t, evaluate j F X n ((f.app X).map n z) t =
      evaluate j F X n ((g.app X).map n z) t) : f = g := by
  apply NatTrans.ext
  funext X
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  exact evaluate_ext j F X n (h X n z)

/-- The original double-loop transpose, including its specified inverse, on a diagram. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/FiniteLoopWords.lean:104"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def transposeIso (F : C ⥤ LoopPrespectrum.{w}) : loopDiagram 2 F ≅ loopDiagram 2 F :=
  NatIso.ofComponents (fun X => LoopTranspose.iso (F.obj X))
    (fun f => LoopTranspose.naturality (F.map f))

/-- The fixed cyclic word first loops the previous word, then swaps the two outer loops. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/FiniteLoopWords.lean:109"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def cyclicIso : ∀ (i : ℕ) (F : C ⥤ LoopPrespectrum.{w}),
    loopDiagram (i + 1) F ≅ loopDiagram (i + 1) F
  | 0, _F => Iso.refl _
  | i + 1, F => Functor.isoWhiskerRight (cyclicIso i F) parameterLoopingFunctor ≪≫
      transposeIso (loopDiagram i F)

/-- The fixed reversal word is the cyclic word followed by the loop of the prior reversal. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/FiniteLoopWords.lean:116"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def reversalIso : ∀ (j : ℕ) (F : C ⥤ LoopPrespectrum.{w}),
    loopDiagram j F ≅ loopDiagram j F
  | 0, F => Iso.refl F
  | j + 1, F => cyclicIso j F ≪≫
      Functor.isoWhiskerRight (reversalIso j F) parameterLoopingFunctor

/-- The fixed cyclic word retains the actual tuple in left-rotated evaluation order. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/FiniteLoopWords.lean:122"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem cyclicIso_evaluate (i : ℕ) (F : C ⥤ LoopPrespectrum.{w}) (X : C) (n : ℕ)
    (z : ((loopDiagram (i + 1) F).obj X).space n) (t : Fin (i + 1) → unitInterval) :
    evaluate (i + 1) F X n (((cyclicIso i F).hom.app X).map n z) t =
      evaluate (i + 1) F X n z (Fin.snoc (Fin.tail t) (t 0)) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    change evaluate (i + 1) F X n
      ((((cyclicIso i F).hom.app X).map n (Path.toContinuousMap z (t 1))))
      (Fin.cons (t 0) (Fin.tail (Fin.tail t))) = _
    rw [ih]
    simp only [Fin.tail_cons, Fin.cons_zero]
    change evaluate (i + 2) F X n z
      (Fin.cons (t 1) (Fin.snoc (Fin.tail (Fin.tail t)) (t 0))) = _
    rw [Fin.cons_snoc_eq_snoc_cons]
    congr 2
    exact Fin.cons_self_tail (Fin.tail t)

/-- The fixed reversal word reverses all finite loop times, leaving the final value intact. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/FiniteLoopWords.lean:141"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem reversalIso_evaluate (j : ℕ) (F : C ⥤ LoopPrespectrum.{w}) (X : C) (n : ℕ)
    (z : ((loopDiagram j F).obj X).space n) (t : Fin j → unitInterval) :
    evaluate j F X n (((reversalIso j F).hom.app X).map n z) t =
      evaluate j F X n z (t ∘ Fin.rev) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change evaluate j F X n (((reversalIso j F).hom.app X).map n
      (Path.toContinuousMap (((cyclicIso j F).hom.app X).map n z) (t 0))) (Fin.tail t) = _
    rw [ih]
    change evaluate (j + 1) F X n (((cyclicIso j F).hom.app X).map n z)
      (Fin.cons (t 0) (Fin.tail t ∘ Fin.rev)) = _
    rw [cyclicIso_evaluate]
    simp only [Fin.tail_cons, Fin.cons_zero]
    congr 1
    rw [← Fin.cons_comp_rev, Fin.cons_self_tail]

/-- Cyclic rotation is natural in every map of diagrams, not only coefficient arrows. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/FiniteLoopWords.lean:159"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def cyclic (i : ℕ) : loopFunctor.{u, v, w} (C := C) (i + 1) ≅ loopFunctor (i + 1) :=
  NatIso.ofComponents (cyclicIso i) (by
    intro F G f
    apply evaluation_hom_ext (i + 1) (E := loopDiagram (i + 1) F) (F := G)
    intro X n z t
    change evaluate (i + 1) G X n
      (((cyclicIso i G).hom.app X).map n (((loopMap (i + 1) f).app X).map n z)) t =
      evaluate (i + 1) G X n (((loopMap (i + 1) f).app X).map n
        (((cyclicIso i F).hom.app X).map n z)) t
    rw [cyclicIso_evaluate, evaluate_loopMap, evaluate_loopMap, cyclicIso_evaluate])

/-- The fixed reversal is a natural isomorphism of the actual finite-loop functor. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/FiniteLoopWords.lean:171"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def reversal (j : ℕ) : loopFunctor.{u, v, w} (C := C) j ≅ loopFunctor j :=
  NatIso.ofComponents (reversalIso j) (by
    intro F G f
    apply evaluation_hom_ext j (E := loopDiagram j F) (F := G)
    intro X n z t
    change evaluate j G X n
      (((reversalIso j G).hom.app X).map n (((loopMap j f).app X).map n z)) t =
      evaluate j G X n (((loopMap j f).app X).map n
        (((reversalIso j F).hom.app X).map n z)) t
    rw [reversalIso_evaluate, evaluate_loopMap, evaluate_loopMap, reversalIso_evaluate])

/-- On two loops the cyclic word is exactly the original transpose. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/FiniteLoopWords.lean:183"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem cyclicIso_one (F : C ⥤ LoopPrespectrum.{w}) :
    cyclicIso 1 F = transposeIso F := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  apply Path.ext
  funext r
  apply Path.ext
  funext s
  rfl

/-- On three loops the postcomposition order is first the inner, then the outer transpose. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/FiniteLoopWords.lean:199"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem cyclicIso_two (F : C ⥤ LoopPrespectrum.{w}) :
    cyclicIso 2 F = Functor.isoWhiskerRight (transposeIso F) parameterLoopingFunctor ≪≫
      transposeIso (loopDiagram 1 F) := by
  change Functor.isoWhiskerRight (cyclicIso 1 F) parameterLoopingFunctor ≪≫ _ = _
  rw [cyclicIso_one]
  rfl

/-- The two-loop reversal is the unchanged original transpose. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/FiniteLoopWords.lean:207"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem reversalIso_two (F : C ⥤ LoopPrespectrum.{w}) :
    reversalIso 2 F = transposeIso F := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  apply Path.ext
  funext r
  apply Path.ext
  funext s
  rfl

/-- The selected three-loop reversal uses the literal inner-outer-inner word. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/FiniteLoopWords.lean:223"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem reversalIso_three (F : C ⥤ LoopPrespectrum.{w}) :
    reversalIso 3 F =
      (Functor.isoWhiskerRight (transposeIso F) parameterLoopingFunctor ≪≫
        transposeIso (loopDiagram 1 F)) ≪≫
      Functor.isoWhiskerRight (transposeIso F) parameterLoopingFunctor := by
  change cyclicIso 2 F ≪≫ Functor.isoWhiskerRight (reversalIso 2 F)
    parameterLoopingFunctor = _
  rw [cyclicIso_two, reversalIso_two]
  rfl

/-- The full reversal acts involutively on every original finite-loop value. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/FiniteLoopWords.lean:234"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem reversalIso_hom_comp (j : ℕ) (F : C ⥤ LoopPrespectrum.{w}) :
    (reversalIso j F).hom ≫ (reversalIso j F).hom = 𝟙 (loopDiagram j F) := by
  apply evaluation_hom_ext j
  intro X n z t
  change evaluate j F X n (((reversalIso j F).hom.app X).map n
    (((reversalIso j F).hom.app X).map n z)) t = evaluate j F X n z t
  rw [reversalIso_evaluate, reversalIso_evaluate]
  congr 1
  funext a
  exact congrArg t (Fin.rev_rev a)

/-- Its specified inverse agrees with the same fixed reversal map. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/FiniteLoopWords.lean:246"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem reversalIso_inv (j : ℕ) (F : C ⥤ LoopPrespectrum.{w}) :
    (reversalIso j F).inv = (reversalIso j F).hom := by
  apply (cancel_epi (reversalIso j F).hom).mp
  rw [Iso.hom_inv_id, reversalIso_hom_comp]

end Topology.LoopPrespectrum.FiniteLoopWords
