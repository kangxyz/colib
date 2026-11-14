/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Algebra equivalence from a split affine pullback

An actual splitting of the affine pullback as copies of the base induces the tensor-product
algebra equivalence. Its components are the pullbacks of functions along the actual sheets.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
namespace AlgebraicGeometry.SplitAffinePullback
universe u
variable {k R A : Type u} [CommRing k] [CommRing R] [CommRing A]
  [Algebra k R] [Algebra k A] {I : Type u} [Finite I]

abbrev baseMap : Spec (.of R) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k R))
abbrev sourceMap : Spec (.of A) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k A))

variable (e : pullback (baseMap (k := k) (R := R)) (sourceMap (k := k) (A := A)) ≅
  ∐ fun _ : I => Spec (.of R))

/-- Reverse the actual split-scheme trivialization to obtain Spec(product)→Spec(tensor). -/
def splitSpecIso : Spec (.of (I → R)) ≅ Spec (.of (R ⊗[k] A)) :=
  (asIso (sigmaSpec (fun _ : I => CommRingCat.of R))).symm ≪≫
    e.symm ≪≫ pullbackSpecIso k R A

/-- Full faithfulness of Spec extracts the actual tensor-to-product ring equivalence. -/
def splitRingEquiv : R ⊗[k] A ≃+* (I → R) :=
  (Scheme.Spec.preimageIso (splitSpecIso e)).unop.commRingCatIsoToRingEquiv

/-- The ith sheet as a map to Spec(A), without choosing any root of the polynomial. -/
def splitSheet (i : I) : Spec (.of R) ⟶ Spec (.of A) :=
  Sigma.ι (fun _ : I => Spec (.of R)) i ≫ e.inv ≫ pullback.snd _ _

/-- The geometric component equation. This is before ΓSpec and has no coercion ambiguity. -/
theorem split_component_scheme (i : I) :
    Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : I => R) i)) ≫
      (splitSpecIso e).hom ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[k] R ⊗[k] A).toRingHom) =
      splitSheet e i := by
  rw [← ι_sigmaSpec (fun _ : I => CommRingCat.of R) i]
  simp only [splitSpecIso, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    Category.assoc, IsIso.hom_inv_id_assoc]
  exact congrArg (fun f => Sigma.ι (fun _ : I => Spec (.of R)) i ≫ e.inv ≫ f)
    (pullbackSpecIso_hom_snd k R A)

/-- Explicit ΓSpec transport for an actual map of affine spectra. -/
theorem preimage_eq_gamma (s : Spec (.of R) ⟶ Spec (.of A)) :
    Spec.preimage s =
      (Scheme.ΓSpecIso (.of A)).inv ≫ s.appTop ≫
        (Scheme.ΓSpecIso (.of R)).hom := by
  have h := Scheme.ΓSpecIso_naturality (Spec.preimage s)
  rw [Spec.map_preimage] at h
  rw [h, Iso.inv_hom_id_assoc]

/-- Recover the actual scheme map from the extracted ring equivalence. -/
theorem map_splitRingEquiv :
    Spec.map (CommRingCat.ofHom (splitRingEquiv e).toRingHom) =
      (splitSpecIso e).hom := by
  change Spec.map (Spec.preimage (splitSpecIso e).hom) = _
  exact Spec.map_preimage _

/-- Component equation as equality of ring morphisms. -/
theorem split_component_ringHom (i : I) :
    CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[k] R ⊗[k] A).toRingHom ≫
      CommRingCat.ofHom (splitRingEquiv e).toRingHom ≫
      CommRingCat.ofHom (Pi.evalRingHom (fun _ : I => R) i) =
        Spec.preimage (splitSheet e i) := by
  apply Spec.map_injective
  simp only [Spec.map_comp, map_splitRingEquiv, Spec.map_preimage]
  exact split_component_scheme e i

/-- Actual elementwise sheet evaluation, not an assumption about a norm. -/
theorem split_component_apply (i : I) (a : A) :
    splitRingEquiv e (1 ⊗ₜ[k] a) i = (Spec.preimage (splitSheet e i)).hom a := by
  exact congrArg (fun f => f.hom a) (split_component_ringHom e i)

variable (he : e.hom ≫ Sigma.desc (fun _ : I => 𝟙 (Spec (.of R))) =
    pullback.fst (baseMap (k := k) (R := R)) (sourceMap (k := k) (A := A)))

include he in
/-- The trivialization being over R forces each component to preserve scalars. -/
theorem split_component_base (i : I) :
    Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : I => R) i)) ≫
      (splitSpecIso e).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[k] A))) = 𝟙 _ := by
  rw [← ι_sigmaSpec (fun _ : I => CommRingCat.of R) i]
  simp only [splitSpecIso, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    Category.assoc, IsIso.hom_inv_id_assoc, pullbackSpecIso_hom_fst']
  rw [← he, Iso.inv_hom_id_assoc, Sigma.ι_comp_desc]

include he in
/-- Actual scalar compatibility of the extracted RingEquiv. -/
theorem splitRingEquiv_commutes (r : R) :
    splitRingEquiv e (algebraMap R (R ⊗[k] A) r) = algebraMap R (I → R) r := by
  funext i
  have h : CommRingCat.ofHom (algebraMap R (R ⊗[k] A)) ≫
      CommRingCat.ofHom (splitRingEquiv e).toRingHom ≫
      CommRingCat.ofHom (Pi.evalRingHom (fun _ : I => R) i) =
        𝟙 (CommRingCat.of R) := by
    apply Spec.map_injective
    simp only [Spec.map_comp, map_splitRingEquiv, Spec.map_id]
    exact split_component_base e he i
  exact congrArg (fun f => f.hom r) h

/-- The desired actual splitting R-algebra equivalence. -/
def splitAlgEquiv : R ⊗[k] A ≃ₐ[R] (I → R) :=
  { splitRingEquiv e with commutes' := splitRingEquiv_commutes e he }

/-- Its component is exactly the sheet's map on global functions. -/
theorem splitAlgEquiv_component (i : I) (a : A) :
    splitAlgEquiv e he (1 ⊗ₜ[k] a) i =
      ((Scheme.ΓSpecIso (.of R)).hom.hom
        ((splitSheet e i).appTop.hom ((Scheme.ΓSpecIso (.of A)).inv.hom a))) := by
  change splitRingEquiv e (1 ⊗ₜ[k] a) i = _
  rw [split_component_apply, preimage_eq_gamma]
  rfl

end AlgebraicGeometry.SplitAffinePullback
