/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.FieldCycleEvaluation
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The diagonal field group as a quotient of zero-cycles

The literal reduced torus zero-cycles modulo the degree-one singular boundary
compute derived diagonal motivic cohomology over a field. The raw cochain
differential carries the sign `(-1)^q` from the shift by `-q`. This sign acts
invertibly on the boundary image.

Adapted from `motivic_source_a6805c4`,
`Motivic/Cohomology/Diagonal/TopDegree.lean:38-234`, using the native alternating
face complex and its existing `q-r` placement.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped Simplicial

universe w u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalTopDegree
open _root_.AlgebraicGeometry.Scheme PresheafWithTransfers

variable (k : Type u) [Field k]

/-- The base-field object in the correspondence category. -/
abbrev point : Cor k := Cor.mk (SmoothSite.base (Spec (.of k)))

/-- Singular chains of the actual reduced transfer torus. -/
abbrev chains (q r : ℕ) : AddCommGrpCat.{u + 1} :=
  sections (reducedTorus k q) (Cor.simplexProduct (point k) r)

/-- The degree-one boundary in the actual singular chain complex. -/
def boundary (q : ℕ) : chains k q 1 →+ chains k q 0 :=
  ((singularObj (reducedTorus k q) (point k)).d 1 0).hom

/-- The boundary is the difference of the two endpoint transfers. -/
theorem boundary_eq_endpoints (q : ℕ) (x : chains k q 1) :
    boundary k q x =
      transfer (reducedTorus k q) ((Cor.simplexProductCosimplicial (point k)).δ (0 : Fin 2)) x -
        transfer (reducedTorus k q)
          ((Cor.simplexProductCosimplicial (point k)).δ (1 : Fin 2)) x := by
  have h : (singularObj (reducedTorus k q) (point k)).d 1 0 =
      transfer (reducedTorus k q) ((Cor.simplexProductCosimplicial (point k)).δ (0 : Fin 2)) -
        transfer (reducedTorus k q)
          ((Cor.simplexProductCosimplicial (point k)).δ (1 : Fin 2)) := by
    rw [singularObj_d]
    simp [Fin.sum_univ_two, sub_eq_add_neg]
  exact ConcreteCategory.congr_hom h x

/-- The quotient of zero-cycles by the actual singular boundaries. -/
abbrev zeroHomology (q : ℕ) := chains k q 0 ⧸ (boundary k q).range

/-- The signed raw top term has zero outgoing differential. -/
theorem raw_outgoing_d_zero (q : ℕ) :
    (motivicRawBaseComplex k q).d q ((q : ℤ) + 1) = 0 := by
  let E := toPresheaf k ⋙ (evaluation _ AddCommGrpCat.{u + 1}).obj
    (op (SmoothSite.base (Spec (.of k))))
  have h : IsZero ((motivicRawBaseComplex k q).X ((q : ℤ) + 1)) := by
    change IsZero (E.obj ((singularCochainComplex (reducedTorus k q) 0).X
      (((q : ℤ) + 1) + -(q : ℤ))))
    exact E.map_isZero (isZero_singularCochainComplex_X (reducedTorus k q) 0 _ (by omega))
  exact h.eq_of_tgt _ _

/-- The canonical class of a top term in raw homology. -/
def rawClass (q : ℕ) : (motivicRawBaseComplex k q).X q ⟶
    (motivicRawBaseComplex k q).homology q :=
  ((motivicRawBaseComplex k q).iCyclesIso q ((q : ℤ) + 1)
      ((ComplexShape.up ℤ).next_eq' (by simp)) (raw_outgoing_d_zero k q)).inv ≫
    (motivicRawBaseComplex k q).homologyπ q

/-- The preceding signed differential vanishes under the canonical class map. -/
theorem differential_rawClass (q : ℕ) :
    (motivicRawBaseComplex k q).d ((q : ℤ) - 1) q ≫ rawClass k q = 0 := by
  rw [rawClass, ← (motivicRawBaseComplex k q).toCycles_i ((q : ℤ) - 1) q]
  simp only [Category.assoc, HomologicalComplex.iCyclesIso_hom_inv_id_assoc,
    HomologicalComplex.toCycles_comp_homologyπ]

/-- Every raw homology class has a representative in the top term. -/
theorem rawClass_surjective (q : ℕ) : Function.Surjective (rawClass k q) := by
  apply (AddCommGrpCat.epi_iff_surjective _).mp
  unfold rawClass
  infer_instance

/-- A raw top-term representative has zero class exactly when it is a signed boundary. -/
theorem rawClass_eq_zero_iff (q : ℕ) (x : (motivicRawBaseComplex k q).X q) :
    rawClass k q x = 0 ↔ ∃ y : (motivicRawBaseComplex k q).X ((q : ℤ) - 1),
      (motivicRawBaseComplex k q).d ((q : ℤ) - 1) q y = x := by
  let K := motivicRawBaseComplex k q
  let S := ShortComplex.mk (K.toCycles ((q : ℤ) - 1) q) (K.homologyπ q)
    (K.toCycles_comp_homologyπ ((q : ℤ) - 1) q)
  have hS : S.Exact := S.exact_of_g_is_cokernel
    (K.homologyIsCokernel ((q : ℤ) - 1) q
      ((ComplexShape.up ℤ).prev_eq' (by simp)))
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := S.ab_exact_iff.mp hS
      (((K.iCyclesIso q ((q : ℤ) + 1)
        ((ComplexShape.up ℤ).next_eq' (by simp)) (raw_outgoing_d_zero k q)).inv) x) hx
    refine ⟨y, ?_⟩
    have h := congrArg (K.iCycles q) hy
    simpa only [S, ← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_i,
      HomologicalComplex.iCyclesIso_inv_hom_id, ConcreteCategory.id_apply] using h
  · rintro ⟨y, rfl⟩
    exact ConcreteCategory.congr_hom (differential_rawClass k q) y

/-- The raw differential carries the shift sign `(-1)^q` in occupied degrees. -/
theorem raw_d (q r t : ℕ) :
    (motivicRawBaseComplex k q).d ((q : ℤ) - r) ((q : ℤ) - t) =
      (-1 : ℤ) ^ q • ((motivicRawBaseComplexXIso k q r).hom ≫
        (singularObj (reducedTorus k q) (point k)).d r t ≫
          (motivicRawBaseComplexXIso k q t).inv) := by
  let E := toPresheaf k ⋙ (evaluation _ AddCommGrpCat.{u + 1}).obj
    (op (SmoothSite.base (Spec (.of k))))
  calc
    _ = E.map (((singularCochainComplex (reducedTorus k q) 0)⟦-(q : ℤ)⟧).d
        ((q : ℤ) - r) ((q : ℤ) - t)) := by
      simp only [CochainComplex.shiftFunctor_obj_d', Units.smul_def, Functor.map_zsmul]
      rfl
    _ = _ := by
      change E.map
          ((((singularComplex (reducedTorus k q)).extend
            (ComplexShape.embeddingUpIntLE 0))⟦-(q : ℤ)⟧).d
              ((q : ℤ) - r) ((q : ℤ) - t)) =
        (-1 : ℤ) ^ q •
          (E.map (_root_.HomologicalComplex.ExtensionSignedShift.shiftedXIso
              (singularComplex (reducedTorus k q)) q r rfl).hom ≫
            E.map ((singularComplex (reducedTorus k q)).d r t) ≫
            E.map (_root_.HomologicalComplex.ExtensionSignedShift.shiftedXIso
              (singularComplex (reducedTorus k q)) q t rfl).inv)
      simpa only [Units.smul_def, Functor.map_zsmul, Functor.map_comp, Int.negOnePow_neg,
        Int.coe_negOnePow_natCast] using
        congrArg (fun f => E.map f)
          (_root_.HomologicalComplex.ExtensionSignedShift.shifted_d
            (singularComplex (reducedTorus k q)) q r t)

/-- The top raw term identified with singular zero-chains. -/
def topTermIso (q : ℕ) : (motivicRawBaseComplex k q).X q ≅ chains k q 0 :=
  motivicRawBaseComplexXIso k q 0

/-- The preceding raw term identified with singular one-chains. -/
def previousTermIso (q : ℕ) :
    (motivicRawBaseComplex k q).X ((q : ℤ) - 1) ≅ chains k q 1 :=
  motivicRawBaseComplexXIso k q 1

/-- The top signed differential is the transported singular boundary with its shift sign. -/
theorem raw_d_top (q : ℕ) :
    (motivicRawBaseComplex k q).d ((q : ℤ) - 1) q =
      (-1 : ℤ) ^ q • ((previousTermIso k q).hom ≫ AddCommGrpCat.ofHom (boundary k q) ≫
        (topTermIso k q).inv) :=
  raw_d k q 1 0

/-- The raw homology class of a literal singular zero-cycle. -/
def singularClass (q : ℕ) : chains k q 0 →+ (motivicRawBaseComplex k q).homology q :=
  (rawClass k q).hom.comp (topTermIso k q).inv.hom

private theorem sign_squared (q : ℕ) : (-1 : ℤ) ^ q * (-1 : ℤ) ^ q = 1 := by
  rw [← mul_pow]
  simp

/-- A zero-cycle has zero raw class exactly when it is an actual singular boundary. -/
theorem singularClass_eq_zero_iff (q : ℕ) (x : chains k q 0) :
    singularClass k q x = 0 ↔ ∃ y : chains k q 1, boundary k q y = x := by
  rw [singularClass, AddMonoidHom.comp_apply, rawClass_eq_zero_iff]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨(-1 : ℤ) ^ q • (previousTermIso k q).hom y, ?_⟩
    have h := congrArg (topTermIso k q).hom hy
    rw [raw_d_top] at h
    change (topTermIso k q).hom
      ((-1 : ℤ) ^ q • (topTermIso k q).inv
        (boundary k q ((previousTermIso k q).hom y))) =
      (topTermIso k q).hom ((topTermIso k q).inv x) at h
    simpa only [map_zsmul, Iso.inv_hom_id_apply] using h
  · rintro ⟨y, rfl⟩
    refine ⟨(-1 : ℤ) ^ q • (previousTermIso k q).inv y, ?_⟩
    rw [raw_d_top]
    change (-1 : ℤ) ^ q • (topTermIso k q).inv
      (boundary k q ((previousTermIso k q).hom
        ((-1 : ℤ) ^ q • (previousTermIso k q).inv y))) = _
    simp only [map_zsmul, Iso.inv_hom_id_apply, ← mul_zsmul, sign_squared, one_zsmul]

/-- Every singular boundary vanishes in raw homology. -/
theorem singularClass_boundary (q : ℕ) (x : chains k q 1) :
    singularClass k q (boundary k q x) = 0 :=
  (singularClass_eq_zero_iff k q _).2 ⟨x, rfl⟩

/-- Every raw class is represented by a singular zero-cycle. -/
theorem singularClass_surjective (q : ℕ) : Function.Surjective (singularClass k q) :=
  (rawClass_surjective k q).comp (ConcreteCategory.bijective_of_isIso (topTermIso k q).inv).2

/-- The kernel of the singular class map is the image of the two-face boundary. -/
theorem singularClass_ker (q : ℕ) : (singularClass k q).ker = (boundary k q).range := by
  ext x
  exact singularClass_eq_zero_iff k q x

/-- The singular zero-cycle quotient is canonically isomorphic to the raw homology. -/
def quotientToRawEquiv (q : ℕ) : zeroHomology k q ≃+ (motivicRawBaseComplex k q).homology q :=
  (QuotientAddGroup.quotientAddEquivOfEq (singularClass_ker k q).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (singularClass k q) (singularClass_surjective k q))

/-- The quotient equivalence preserves each singular zero-cycle class. -/
theorem quotientToRawEquiv_mk (q : ℕ) (x : chains k q 0) :
    quotientToRawEquiv k q (QuotientAddGroup.mk x) = singularClass k q x := rfl

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The singular zero-cycle quotient computes derived diagonal motivic cohomology. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/Diagonal/TopDegree.lean:38-234"
  "adaptation" "Diagonal cohomology from the literal reduced torus zero-cycle quotient"]
def quotientToMotivicEquiv (q : ℕ) : zeroHomology k q ≃+
    motivicCohomology k q q (SmoothSite.base (Spec (.of k))) :=
  (quotientToRawEquiv k q).trans (motivicRawBaseEvaluationComparison k q q).symm

/-- A singular zero-cycle coset has its corresponding derived class. -/
theorem quotientToMotivicEquiv_mk (q : ℕ) (x : chains k q 0) :
    motivicRawBaseEvaluationComparison k q q
      (quotientToMotivicEquiv k q (QuotientAddGroup.mk x)) = singularClass k q x :=
  (motivicRawBaseEvaluationComparison k q q).apply_symm_apply _

end AlgebraicGeometry.MotivicCohomology.DiagonalTopDegree
