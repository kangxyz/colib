/-
Copyright (c) 2026 Motivic Cohomology contributors and Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.FinitePointEvaluation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Evaluation of an actual finite fundamental cycle by residue norms

Each native fundamental coefficient multiplies the norm of the ordered unit tuple in the
residue field of the original point. This retains nonreduced local lengths and also handles
points with the same image in the torus.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open Function.locallyFinsuppWithin

attribute [local instance] Classical.propDecidable

universe u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalResiduePointEvaluation

open _root_.AlgebraicGeometry.Scheme
open DiagonalPointNorm DiagonalFinitePointEvaluation

variable {k : Type u} [Field k] {T : Scheme.{u}} {q : ℕ}

private theorem fromSpecResidueField_appTop (x : T) :
    (T.fromSpecResidueField x).appTop ≫ (Scheme.ΓSpecIso (T.residueField x)).hom =
      T.Γevaluation x := by
  rw [Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop, Category.assoc,
    Scheme.ΓSpecIso_naturality, Scheme.fromSpecStalk_appTop]
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, Category.comp_id,
    Category.assoc, Iso.inv_hom_id_assoc]
  exact T.germ_residue (U := ⊤) x trivial

/-- The structural scalar map in the actual residue field. -/
def residueScalar (p : T ⟶ Spec (.of k)) (x : T) : k →+* T.residueField x :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ T.Γevaluation x).hom

/-- The algebra action induced by the given map to the base. -/
abbrev residueAlgebra (p : T ⟶ Spec (.of k)) (x : T) : Algebra k (T.residueField x) :=
  (residueScalar p x).toAlgebra

/-- The structural map from the residue point is the spectrum of this scalar map. -/
theorem residue_projection (p : T ⟶ Spec (.of k)) (x : T) :
    T.fromSpecResidueField x ≫ p = Spec.map (CommRingCat.ofHom (residueScalar p x)) := by
  apply ext_of_isAffine
  apply (cancel_mono (Scheme.ΓSpecIso (T.residueField x)).hom).mp
  rw [Scheme.Hom.comp_appTop, Category.assoc, fromSpecResidueField_appTop,
    Scheme.ΓSpecIso_naturality]
  change p.appTop ≫ T.Γevaluation x =
    (Scheme.ΓSpecIso (.of k)).hom ≫ (Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ T.Γevaluation x
  simp only [Iso.hom_inv_id_assoc]

/-- Finiteness over the base makes the original scheme Artinian. -/
theorem finiteSchemeArtinian (p : T ⟶ Spec (.of k)) [IsFinite p] : IsArtinianScheme T where
  toIsLocallyArtinian := .of_locallyQuasiFinite p
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace p

/-- Index the sum by all actual points of the original finite scheme. -/
abbrev finiteSchemeFintype (p : T ⟶ Spec (.of k)) [IsFinite p] : Fintype T := by
  letI : IsArtinianScheme T := finiteSchemeArtinian p
  exact Fintype.ofFinite T

private theorem residueClosed [DiscreteTopology T] (x : T) :
    IsClosedImmersion (T.fromSpecResidueField x) :=
  isClosed_singleton_iff_isClosedImmersion.mp (isClosed_discrete _)

/-- The finite residue extension uses the actual structural action. -/
theorem residueFinite (p : T ⟶ Spec (.of k)) [IsFinite p] (x : T) :
    let := residueAlgebra p x
    Module.Finite k (T.residueField x) := by
  let := residueAlgebra p x
  let : IsArtinianScheme T := finiteSchemeArtinian p
  let := residueClosed x
  have h : IsFinite (Spec.map (CommRingCat.ofHom (residueScalar p x))) := by
    rw [← residue_projection]
    infer_instance
  exact RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp h)

/-- The coordinates restrict to their actual values in the residue field of the point. -/
theorem residue_coordinate (j : T ⟶ ambient k q) (x : T) (i : Fin q) :
    affineCoordinateUnit (T.fromSpecResidueField x ≫ j) i =
      Units.map (T.Γevaluation x).hom.toMonoidHom (schemeCoordinateUnit j i) := by
  apply Units.ext
  rw [affineCoordinateUnit, schemeCoordinateUnit_comp]
  exact ConcreteCategory.congr_hom (fromSpecResidueField_appTop x)
    (schemeCoordinateUnit j i).val

/-- The native norm of a tuple evaluated in one actual residue field. -/
def residueValue (p : T ⟶ Spec (.of k)) [IsFinite p]
    (a : Fin q → Γ(T, ⊤)ˣ) (x : T) : MilnorKTheory k q := by
  letI := residueAlgebra p x
  letI := residueFinite p x
  exact milnorKNorm k (T.residueField x) q
    (milnorKTupleSymbol fun i => Units.map (T.Γevaluation x).hom.toMonoidHom (a i))

private theorem cycle_eq_sum_single [Fintype T] [DecidableEq T] (c : AlgebraicCycle T ℤ) :
    c = ∑ x : T, single x (c x) := by
  apply Function.locallyFinsuppWithin.ext
  intro x
  simp [Finset.sum_apply]

section ResiduePoint

variable (p : T ⟶ Spec (.of k)) [IsFinite p] (j : T ⟶ ambient k q) [IsFinite j]
  (hp : j ≫ pullback.fst _ _ = p)

omit [IsFinite p] [IsFinite j] in
include hp in
private theorem residuePoint_projection (x : T) :
    (T.fromSpecResidueField x ≫ j) ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (residueScalar p x)) := by
  rw [Category.assoc, hp, residue_projection]

private def residuePointCycle (x : T) (n : ℤ) :
    finiteCorrespondences (𝟙 (Spec (.of k))) (SmoothSite.torusPower (Spec (.of k)) q).hom := by
  letI := finiteSchemeArtinian p
  letI := residueClosed x
  letI := residueAlgebra p x
  letI := residueFinite p x
  let m := T.fromSpecResidueField x ≫ j
  let Z : Generator k q :=
    imageGenerator (E := T.residueField x) m (residuePoint_projection p j hp x)
  exact singleFiniteCorrespondence _ _ Z.val Z.property
    (n * (m.residueDegree (genericPoint (Spec (T.residueField x))) : ℤ))

private theorem residuePointCycle_val (x : T) (n : ℤ) :
    (residuePointCycle p j hp x n).val = finiteCyclePushforward j (single x n) := by
  let := finiteSchemeArtinian p
  let := residueClosed x
  let m := T.fromSpecResidueField x ≫ j
  let y := genericPoint (Spec (T.residueField x))
  have hy : T.fromSpecResidueField x y = x := Scheme.fromSpecResidueField_apply _ _
  have hdeg : m.residueDegree y = j.residueDegree x := by
    simpa only [residueDegree_eq_one_of_isClosedImmersion, mul_one, hy] using
      residueDegree_comp (T.fromSpecResidueField x) j y
  calc
    (residuePointCycle p j hp x n).val = single (m y) (n * (m.residueDegree y : ℤ)) := rfl
    _ = single (j x) (n * (j.residueDegree x : ℤ)) := by
      rw [hdeg]
      change single (j (T.fromSpecResidueField x y)) _ = _
      rw [hy]
    _ = finiteCyclePushforward j (single x n) := (finiteCyclePushforward_single j x n).symm

private theorem cycleValue_residuePointCycle [CharZero k]
    (a : Fin q → Γ(T, ⊤)ˣ) (ha : ∀ i, schemeCoordinateUnit j i = a i) (x : T) (n : ℤ) :
    cycleValue k q (residuePointCycle p j hp x n) = n • residueValue p a x := by
  let := finiteSchemeArtinian p
  let := residueClosed x
  let := residueAlgebra p x
  let := residueFinite p x
  let m := T.fromSpecResidueField x ≫ j
  have hm := residuePoint_projection p j hp x
  have hn := cycleValue_single_image (E := T.residueField x) m hm n
  refine hn.trans (congrArg (fun v : MilnorKTheory k q => n • v) ?_)
  change milnorKNorm k (T.residueField x) q (milnorKTupleSymbol (affineCoordinateUnit m)) =
    milnorKNorm k (T.residueField x) q
      (milnorKTupleSymbol fun i => Units.map (T.Γevaluation x).hom.toMonoidHom (a i))
  apply congrArg (fun b : Fin q → (T.residueField x)ˣ =>
    milnorKNorm k (T.residueField x) q (milnorKTupleSymbol b))
  funext i
  change affineCoordinateUnit (T.fromSpecResidueField x ≫ j) i = _
  rw [residue_coordinate, ha]

include hp in
private theorem cycleValue_eq_residue_sum [CharZero k] [Fintype T]
    (a : Fin q → Γ(T, ⊤)ˣ) (ha : ∀ i, schemeCoordinateUnit j i = a i)
    (α : finiteCorrespondences (𝟙 (Spec (.of k))) (SmoothSite.torusPower (Spec (.of k)) q).hom)
    (c : AlgebraicCycle T ℤ) (hα : α.val = finiteCyclePushforward j c) :
    cycleValue k q α = ∑ x : T, c x • residueValue p a x := by
  let s (x : T) := residuePointCycle p j hp x (c x)
  let β := ∑ x : T, s x
  have hβ : β.val = finiteCyclePushforward j c := by
    calc
      β.val = ∑ x : T, (s x).val :=
        map_sum (finiteCorrespondences _ _).subtype s Finset.univ
      _ = ∑ x : T, finiteCyclePushforward j (single x (c x)) :=
        Finset.sum_congr rfl fun x _ => residuePointCycle_val p j hp x (c x)
      _ = finiteCyclePushforward j (∑ x : T, single x (c x)) :=
        (map_sum (finiteCyclePushforward j) (fun x : T => single x (c x)) Finset.univ).symm
      _ = finiteCyclePushforward j c :=
        congrArg (finiteCyclePushforward j) (cycle_eq_sum_single c).symm
  have he : α = β := Subtype.ext (hα.trans hβ.symm)
  calc
    cycleValue k q α = cycleValue k q β := congrArg (cycleValue k q) he
    _ = ∑ x : T, cycleValue k q (s x) := map_sum (cycleValue k q) s Finset.univ
    _ = _ := Finset.sum_congr rfl fun x _ => cycleValue_residuePointCycle p j hp a ha x (c x)

include hp in
/-- The finite fundamental pushforward evaluates as the full local-length-weighted residue
norm sum, with all the specified original unit coordinates. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/Diagonal/ResiduePointEvaluation.lean:146-213" "adaptation"
  "Evaluation of the native finite fundamental pushforward by actual residue norms"]
theorem cycleValue_eq_residue_sum_of_finite [CharZero k]
    (a : Fin q → Γ(T, ⊤)ˣ) (ha : ∀ i, schemeCoordinateUnit j i = a i)
    (α : finiteCorrespondences (𝟙 (Spec (.of k))) (SmoothSite.torusPower (Spec (.of k)) q).hom)
    (hα : let := finiteSchemeArtinian p
      α.val = finiteCyclePushforward j (AlgebraicCycle.fundamentalCycle T)) :
    let := finiteSchemeArtinian p
    let := finiteSchemeFintype p
    cycleValue k q α = ∑ x : T, AlgebraicCycle.fundamentalCycle T x • residueValue p a x := by
  let := finiteSchemeArtinian p
  let := finiteSchemeFintype p
  exact cycleValue_eq_residue_sum p j hp a ha α (AlgebraicCycle.fundamentalCycle T) hα

end ResiduePoint

end AlgebraicGeometry.MotivicCohomology.DiagonalResiduePointEvaluation
