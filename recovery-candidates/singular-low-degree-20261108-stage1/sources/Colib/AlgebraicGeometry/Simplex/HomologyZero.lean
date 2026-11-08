/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Simplex.Exactness
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# The actual degree-zero quotient of ordinary algebraic singular chains

The homology object is the existing native homology of `singularChainsFunctor`.
Its canonical map from degree zero is the native opcycle projection followed
by `ChainComplex.isoHomologyι₀.inv`. This map coequalizes the original two
geometric faces and is universal for that relation. No new quotient or chain
carrier is introduced. Degree zero is kept as the literal `P(U × Δ⁰)`; this
file does not silently identify the zero simplex with the base.

The construction in MVW2006, Definition 2.14, printed p. 16, is background.
The quotient and its universal property below are native categorical
consequences of that ordinary construction, over any commutative base ring
and any abelian coefficient category. They assert neither transfers nor a
comparison with motivic cohomology.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite AlgebraicTopology
open AlgebraicGeometry.Scheme
open scoped Simplicial

universe u v w

namespace AlgebraicSimplex

variable (R : Type u) [CommRing R]
variable {A : Type v} [Category.{w} A] [Abelian A]
variable (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A)

/-- The original zero-chain projection onto the native zeroth homology. -/
def singularHomologyZeroπ :
    ((singularChainsFunctor R).obj P).X 0 ⟶
      ((singularChainsFunctor R).obj P).homology 0 :=
  ((singularChainsFunctor R).obj P).pOpcycles 0 ≫
    ((singularChainsFunctor R).obj P).isoHomologyι₀.inv

instance : Epi (singularHomologyZeroπ R P) := by
  dsimp [singularHomologyZeroπ]
  infer_instance

/-- The original degree-one differential is killed by the class map. -/
theorem singularChains_d_comp_homologyZeroπ :
    ((singularChainsFunctor R).obj P).d 1 0 ≫ singularHomologyZeroπ R P = 0 := by
  simp [singularHomologyZeroπ]

/-- The two original barycentric face restrictions have the same homology class. -/
theorem singularFaces_comp_homologyZeroπ :
    (simplicialPresheaf R P).δ (0 : Fin 2) ≫ singularHomologyZeroπ R P =
      (simplicialPresheaf R P).δ (1 : Fin 2) ≫ singularHomologyZeroπ R P := by
  have h := singularChains_d_comp_homologyZeroπ R P
  have hd : ((singularChainsFunctor R).obj P).d 1 0 =
      (simplicialPresheaf R P).δ (0 : Fin 2) -
        (simplicialPresheaf R P).δ (1 : Fin 2) := by
    ext U
    exact singularChainsFunctor_obj_d_one_zero_app R P U
  rw [hd] at h
  have he := Preadditive.sub_comp
    ((simplicialPresheaf R P).δ (0 : Fin 2))
    ((simplicialPresheaf R P).δ (1 : Fin 2)) (singularHomologyZeroπ R P)
  exact sub_eq_zero.mp (he.symm.trans h)

/-- A morphism constant on the two actual faces kills the singular differential. -/
theorem singularChains_d_comp_eq_zero_iff
    {Q : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A}
    (f : ((singularChainsFunctor R).obj P).X 0 ⟶ Q) :
    ((singularChainsFunctor R).obj P).d 1 0 ≫ f = 0 ↔
      (simplicialPresheaf R P).δ (0 : Fin 2) ≫ f =
        (simplicialPresheaf R P).δ (1 : Fin 2) ≫ f := by
  have hd : ((singularChainsFunctor R).obj P).d 1 0 =
      (simplicialPresheaf R P).δ (0 : Fin 2) -
        (simplicialPresheaf R P).δ (1 : Fin 2) := by
    ext U
    exact singularChainsFunctor_obj_d_one_zero_app R P U
  rw [hd]
  have he := Preadditive.sub_comp
    ((simplicialPresheaf R P).δ (0 : Fin 2))
    ((simplicialPresheaf R P).δ (1 : Fin 2)) f
  exact (Iff.of_eq (congrArg (fun g => g = 0) he)).trans sub_eq_zero

/-- The native universal descent of a morphism that identifies the two faces. -/
def singularHomologyZeroDesc {Q : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A}
    (f : ((singularChainsFunctor R).obj P).X 0 ⟶ Q)
    (hf : (simplicialPresheaf R P).δ (0 : Fin 2) ≫ f =
      (simplicialPresheaf R P).δ (1 : Fin 2) ≫ f) :
    ((singularChainsFunctor R).obj P).homology 0 ⟶ Q :=
  ((singularChainsFunctor R).obj P).isoHomologyι₀.hom ≫
    ((singularChainsFunctor R).obj P).descOpcycles f 1 (by simp)
      ((singularChains_d_comp_eq_zero_iff R P f).2 hf)

/-- The descended map has the prescribed value on the actual zero chains. -/
theorem singularHomologyZeroπ_desc {Q : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A}
    (f : ((singularChainsFunctor R).obj P).X 0 ⟶ Q)
    (hf : (simplicialPresheaf R P).δ (0 : Fin 2) ≫ f =
      (simplicialPresheaf R P).δ (1 : Fin 2) ≫ f) :
    singularHomologyZeroπ R P ≫ singularHomologyZeroDesc R P f hf = f := by
  simp [singularHomologyZeroπ, singularHomologyZeroDesc]

/-- Maps out of the native zeroth homology are determined on actual zero chains. -/
theorem singularHomologyZero_hom_ext {Q : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A}
    {f g : ((singularChainsFunctor R).obj P).homology 0 ⟶ Q}
    (h : singularHomologyZeroπ R P ≫ f = singularHomologyZeroπ R P ≫ g) : f = g :=
  (cancel_epi (singularHomologyZeroπ R P)).1 h

/-- Exact universal property for the original two geometric face restrictions. -/
@[colib_ref "MVW2006" "Lecture 2, Definition 2.14, p. 16"
  "background" "Ordinary singular chains whose native zeroth homology is presented here"]
theorem existsUnique_singularHomologyZeroDesc
    {Q : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A}
    (f : ((singularChainsFunctor R).obj P).X 0 ⟶ Q)
    (hf : (simplicialPresheaf R P).δ (0 : Fin 2) ≫ f =
      (simplicialPresheaf R P).δ (1 : Fin 2) ≫ f) :
    ∃! g : ((singularChainsFunctor R).obj P).homology 0 ⟶ Q,
      singularHomologyZeroπ R P ≫ g = f := by
  refine ⟨singularHomologyZeroDesc R P f hf, singularHomologyZeroπ_desc R P f hf, ?_⟩
  intro g hg
  exact singularHomologyZero_hom_ext R P (hg.trans (singularHomologyZeroπ_desc R P f hf).symm)

/-- The actual zero-chain projection is natural in the original coefficient map. -/
theorem singularHomologyZeroπ_naturality
    {P Q : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A} (α : P ⟶ Q) :
    singularHomologyZeroπ R P ≫
      HomologicalComplex.homologyMap ((singularChainsFunctor R).map α) 0 =
        ((singularChainsFunctor R).map α).f 0 ≫ singularHomologyZeroπ R Q := by
  simp only [singularHomologyZeroπ, Category.assoc,
    ChainComplex.isoHomologyι₀_inv_naturality,
    HomologicalComplex.p_opcyclesMap_assoc]

end AlgebraicSimplex
