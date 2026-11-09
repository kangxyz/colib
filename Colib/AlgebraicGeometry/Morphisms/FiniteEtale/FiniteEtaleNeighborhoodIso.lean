/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.DescentFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.SingletonFibre

/-!
# Isomorphism neighborhoods of finite étale morphisms

An actual residue-field isomorphism gives a section of the scheme-theoretic
fiber map. If the étale fiber has only that point, this section is a surjective
open immersion and hence an isomorphism. For a finite étale morphism, local
constancy of its rank then extends the isomorphism to a Zariski neighborhood.
No reducedness or connectedness assumption on the base is needed.

Implementation adapted from
`Motivic/Aglib/AlgebraicGeometry/Morphisms/FiniteEtale/FiniteEtaleNeighborhoodIso.lean`
at motivic commit a6805c4a87cdfd7717dd7a94039246a167f15380.
The section-open-immersion theorem and the rank-one neighborhood theorem are
reused from their native Stacks owners, rather than reproved here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}

/-- The section of the actual fiber map induced by the inverse of the actual
residue-field map at a rational point. -/
def fiberSectionOfResidueFieldIso (f : X ⟶ Y) (x : X) [IsIso (f.residueFieldMap x)] :
    Spec (Y.residueField (f x)) ⟶ f.fiber (f x) :=
  Spec.map (inv (f.residueFieldMap x)) ≫ f.asFiberHom x

@[reassoc (attr := simp)]
lemma fiberSectionOfResidueFieldIso_fiberToSpecResidueField
    (f : X ⟶ Y) (x : X) [IsIso (f.residueFieldMap x)] :
    f.fiberSectionOfResidueFieldIso x ≫ f.fiberToSpecResidueField (f x) = 𝟙 _ := by
  rw [fiberSectionOfResidueFieldIso, Category.assoc,
    asFiberHom_fiberToSpecResidueField, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id]

/-- An étale fiber with only one point and with isomorphic actual residue-field
map is isomorphic to the spectrum of the base residue field. -/
theorem isIso_fiberToSpecResidueField_of_singleton
    (f : X ⟶ Y) [Etale f] (x : X) [IsIso (f.residueFieldMap x)]
    (h : ∀ x' : X, f x' = f x → x' = x) :
    IsIso (f.fiberToSpecResidueField (f x)) := by
  let s := f.fiberSectionOfResidueFieldIso x
  have hs : s ≫ f.fiberToSpecResidueField (f x) = 𝟙 _ :=
    f.fiberSectionOfResidueFieldIso_fiberToSpecResidueField x
  have : Etale (f.fiberToSpecResidueField (f x)) :=
    inferInstanceAs (Etale (pullback.snd f (Y.fromSpecResidueField (f x))))
  have : IsOpenImmersion s :=
    isOpenImmersion_of_section_of_etale _ s hs
  have : Surjective s := ⟨fun z ↦ by
    refine ⟨IsLocalRing.closedPoint _, ?_⟩
    apply (f.fiberι (f x)).isEmbedding.injective
    have hz : f (f.fiberι (f x) z) = f x := (f.fiberHomeo (f x) z).property
    change f.fiberι (f x) ((f.asFiberHom x) _) = f.fiberι (f x) z
    rw [asFiberHom_apply, fiberι_asFiber]
    exact (h _ hz).symm⟩
  have : IsIso s := (isIso_iff_isOpenImmersion_and_surjective s).mpr ⟨inferInstance, inferInstance⟩
  have : IsIso (s ≫ f.fiberToSpecResidueField (f x)) := by rw [hs]; infer_instance
  exact IsIso.of_isIso_comp_left (f := s) _

/-- Under the singleton hypothesis, the rational-point section is also a left
inverse of the actual scheme-theoretic fiber map. -/
lemma fiberToSpecResidueField_fiberSectionOfResidueFieldIso
    (f : X ⟶ Y) [Etale f] (x : X) [IsIso (f.residueFieldMap x)]
    (h : ∀ x' : X, f x' = f x → x' = x) :
    f.fiberToSpecResidueField (f x) ≫ f.fiberSectionOfResidueFieldIso x = 𝟙 _ := by
  have := f.isIso_fiberToSpecResidueField_of_singleton x h
  apply (cancel_mono (f.fiberToSpecResidueField (f x))).mp
  simp

/-- An isomorphism on the actual fiber of a finite flat morphism of finite
presentation extends to an isomorphism on a Zariski neighborhood. -/
theorem exists_isIso_morphismRestrict_of_isIso_fiber
    (f : X ⟶ Y) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]
    (y : Y) [IsIso (f.fiberToSpecResidueField y)] :
    ∃ U : Y.Opens, y ∈ U ∧ IsIso (f ∣_ U) := by
  apply AlgebraicGeometry.exists_open_restrict_isIso_of_finrank_eq_one f y
  let z : Spec (Y.residueField y) := IsLocalRing.closedPoint _
  have h := finrank_pullback_snd f (Y.fromSpecResidueField y) z
  change (f.fiberToSpecResidueField y).finrank _ = _ at h
  rw [Y.fromSpecResidueField_apply] at h
  rw [← h, finrank_eq_one_of_isIso]
  rfl

/-- A finite étale morphism with exactly one point over `y`, whose actual
residue-field map is an isomorphism, is an isomorphism near `y`.
The base may be nonreduced or disconnected. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Morphisms/FiniteEtale/FiniteEtaleNeighborhoodIso.lean:120-130"
  "adaptation" "Finite etale singleton-fiber isomorphism neighborhoods over arbitrary schemes"]
theorem exists_isIso_morphismRestrict_of_singleton
    (f : X ⟶ Y) [IsFinite f] [Etale f] (y : Y) (x : X) (hx : f x = y)
    (h : ∀ x' : X, f x' = y → x' = x) (hres : IsIso (f.residueFieldMap x)) :
    ∃ U : Y.Opens, y ∈ U ∧ IsIso (f ∣_ U) := by
  subst y
  let := hres
  have := f.isIso_fiberToSpecResidueField_of_singleton x h
  exact f.exists_isIso_morphismRestrict_of_isIso_fiber (f x)

end AlgebraicGeometry.Scheme.Hom
