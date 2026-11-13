/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.WholeFiniteFlatEndpoint
public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.RelativePolynomial
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.WholeFibers
public import Colib.AlgebraicGeometry.Scheme.PolynomialQuotient.TargetBaseChange
public import Colib.AlgebraicGeometry.Sites.Smooth.Affine.LineCoordinates

/-!
# Whole polynomial endpoints in a relative principal open

The inner polynomial variable is the native cylinder parameter. At an
endpoint the entire quotient scheme is the coefficient base change.
Both span projections agree with that base change.

Adapted from `Motivic/AlgebraicGeometry/Correspondences/Moving/Polynomial/Relative/`
at `motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`, files
`PencilEndpoints.lean` and `PencilSpecialization.lean`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite

open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.SmoothSite.Contraction
open _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
open _root_.AlgebraicGeometry.Scheme.PolynomialSectionPencil

section Coefficients

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- The coefficient ring map fixes the original coefficients along the cylinder. -/
abbrev parameterCoefficients : R →+* A[X] := C.comp (algebraMap R A)

end Coefficients

variable {k R A : Type u} [Field k] [CommRing R] [CommRing A]
  [Algebra k R] [Algebra.Smooth k R] [Algebra R A] [Algebra k A]
  [IsScalarTower k R A] [Algebra.Smooth k A]

local notation "U" => sourceSite (k := k) (A := A)
local notation "W" => lineSite (k := k) (R := R)
local notation "e" => lineCylinderIso (k := k) (R := A)
local notation "b₀" => Spec.map (CommRingCat.ofHom (algebraMap k R))

omit [Algebra.Smooth k R] in
private theorem parameterCoefficients_base :
    Spec.map (CommRingCat.ofHom (parameterCoefficients (R := R) (A := A))) ≫ b₀ =
      (lineSite (k := k) (R := A)).hom := by
  change Spec.map (CommRingCat.ofHom (parameterCoefficients (R := R) (A := A))) ≫ b₀ =
    Spec.map (CommRingCat.ofHom (C : A →+* A[X])) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k A))
  have h : CommRingCat.ofHom (algebraMap k R) ≫
        CommRingCat.ofHom (parameterCoefficients (R := R) (A := A)) =
      CommRingCat.ofHom (algebraMap k A) ≫ CommRingCat.ofHom (C : A →+* A[X]) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change C (algebraMap R A (algebraMap k R x)) = C (algebraMap k A x)
    exact congrArg C
      (congrArg (fun f : k →+* A => f x) (IsScalarTower.algebraMap_eq k R A).symm)
  rw [← Spec.map_comp, ← Spec.map_comp, h]

private theorem polynomialFamily_line_base (p : A[X][X]) :
    source p ≫ (lineSite (k := k) (R := A)).hom =
      target (parameterCoefficients (R := R) (A := A)) p ≫ (W).hom := by
  rw [← parameterCoefficients_base (k := k) (R := R) (A := A)]
  change source p ≫
      (Spec.map (CommRingCat.ofHom (parameterCoefficients (R := R) (A := A))) ≫ b₀) =
    target (parameterCoefficients (R := R) (A := A)) p ≫ (polynomialProjection (.of R) ≫ b₀)
  rw [← Category.assoc, ← Category.assoc, target_base]

/-- The full monic quotient maps to the original native additive cylinder. -/
def polynomialFamilySource (p : A[X][X]) :
    Spec (.of (AdjoinRoot p)) ⟶ (affineLineCylinder.obj U).left :=
  source p ≫ (e).hom.left

private theorem polynomialFamily_affine_base (p : A[X][X]) :
    polynomialFamilySource (k := k) p ≫ (affineLineCylinder.obj U).hom =
      target (parameterCoefficients (R := R) (A := A)) p ≫ (W).hom := by
  rw [polynomialFamilySource, Category.assoc, MorphismProperty.Over.w (e).hom]
  exact polynomialFamily_line_base p

/-- Both polynomial-family legs have the original ground-field structure map. -/
theorem polynomialFamily_open_base (p : A[X][X]) (f : R[X])
    (hf : IsUnit (AdjoinRoot.mk p (f.map (parameterCoefficients (R := R) (A := A))))) :
    polynomialFamilySource (k := k) p ≫ (affineLineCylinder.obj U).hom =
      openTarget (parameterCoefficients (R := R) (A := A)) p f hf ≫
        (openSite (k := k) f).hom := by
  change _ = openTarget _ p f hf ≫ ((principalOpen f).ι ≫ (W).hom)
  rw [← Category.assoc, openTarget_inclusion]
  exact polynomialFamily_affine_base p

/-- A monic polynomial family has a finite-flat source over the actual cylinder. -/
theorem polynomialFamilySource_finite_flat (p : A[X][X]) (hp : p.Monic) :
    IsFinite (polynomialFamilySource (k := k) p) ∧ Flat (polynomialFamilySource (k := k) p) := by
  let := source_finite p hp
  let := source_flat p hp
  let : IsIso (e).hom.left :=
    inferInstanceAs (IsIso ((Scheme.SmoothSite.forgetScheme _).mapIso e).hom)
  change IsFinite (source p ≫ (e).hom.left) ∧ Flat (source p ≫ (e).hom.left)
  exact ⟨inferInstance, inferInstance⟩

/-- The whole monic polynomial family into the unchanged relative open. -/
def openPolynomialFamily (p : A[X][X]) (hp : p.Monic) (f : R[X])
    (hf : IsUnit (AdjoinRoot.mk p (f.map (parameterCoefficients (R := R) (A := A))))) :
    Cor.mk (affineLineCylinder.obj U) ⟶ Cor.mk (openSite (k := k) f) := by
  obtain ⟨hfin, hflat⟩ := polynomialFamilySource_finite_flat (k := k) p hp
  exact Cor.ofFiniteFlatSpan (polynomialFamilySource (k := k) p)
    (openTarget (parameterCoefficients (R := R) (A := A)) p f hf)
    (polynomialFamily_open_base p f hf)

private theorem polynomialFamily_pair_closed (p : A[X][X]) :
    IsClosedImmersion (pullback.lift (polynomialFamilySource (k := k) p)
      (target (parameterCoefficients (R := R) (A := A)) p) (polynomialFamily_affine_base p)) := by
  let σ := parameterCoefficients (R := R) (A := A)
  let c := (lineSite (k := k) (R := A)).hom
  let b := (affineLineCylinder.obj U).hom
  have hc : Spec.map (CommRingCat.ofHom σ) ≫ b₀ = c :=
    parameterCoefficients_base (k := k) (R := R) (A := A)
  let i := (pullback.congrHom hc (rfl : polynomialProjection (.of R) ≫ b₀ = (W).hom)).hom
  let n : Spec (.of A[X][X]) ⟶ pullback c (W).hom := relativePolynomialAmbient σ b₀ ≫ i
  have hif : i ≫ pullback.fst c (W).hom =
      pullback.fst (Spec.map (CommRingCat.ofHom σ) ≫ b₀) (polynomialProjection (.of R) ≫ b₀) := by
    simp only [i, pullback.congrHom_hom, pullback.map]
    erw [pullback.lift_fst, Category.comp_id]
  have his : i ≫ pullback.snd c (W).hom =
      pullback.snd (Spec.map (CommRingCat.ofHom σ) ≫ b₀) (polynomialProjection (.of R) ≫ b₀) := by
    simp only [i, pullback.congrHom_hom, pullback.map]
    erw [pullback.lift_snd, Category.comp_id]
  let : IsAffineHom b₀ := isAffineHom_of_isAffine b₀
  let : IsClosedImmersion n := by
    dsimp only [n]
    infer_instance
  have hn : pullback.lift (source p) (target σ p) (polynomialFamily_line_base (k := k) p) =
      inclusion p ≫ n := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      dsimp only [n]
      rw [Category.assoc, Category.assoc, hif, relativePolynomialAmbient_fst]
      exact (inclusion_projection p).symm
    · rw [pullback.lift_snd]
      dsimp only [n]
      rw [Category.assoc, Category.assoc, his, relativePolynomialAmbient_snd]
      rfl
  have he : (e).inv.left ≫ c = b := MorphismProperty.Over.w (e).inv
  let : IsIso (e).inv.left := inferInstanceAs
    (IsIso ((Scheme.SmoothSite.forgetScheme _).mapIso e).inv)
  let m := pullback.map b (W).hom c (W).hom (e).inv.left (𝟙 _) (𝟙 _)
    (by simpa only [Category.comp_id] using he.symm) (by simp)
  let : IsIso m := by dsimp only [m]; infer_instance
  have hmf : m ≫ pullback.fst c (W).hom =
      pullback.fst b (W).hom ≫ (e).inv.left := by
    dsimp only [m, pullback.map]
    exact pullback.lift_fst _ _ _
  have hms : m ≫ pullback.snd c (W).hom = pullback.snd b (W).hom := by
    dsimp only [m, pullback.map]
    erw [pullback.lift_snd, Category.comp_id]
  have he' : (e).hom.left ≫ (e).inv.left = 𝟙 (Spec (.of A[X])) :=
    congrArg (fun f => f.left) (e).hom_inv_id
  have hm : pullback.lift (polynomialFamilySource (k := k) p)
      (target σ p) (polynomialFamily_affine_base (k := k) p) ≫ m =
      pullback.lift (source p) (target σ p) (polynomialFamily_line_base (k := k) p) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hmf]
      erw [pullback.lift_fst_assoc, pullback.lift_fst]
      rw [polynomialFamilySource, Category.assoc, he', Category.comp_id]
    · simp only [Category.assoc, hms]
      erw [pullback.lift_snd, pullback.lift_snd]
  let : IsClosedImmersion (pullback.lift (polynomialFamilySource (k := k) p)
      (target σ p) (polynomialFamily_affine_base (k := k) p) ≫ m) := by
    rw [hm, hn]
    infer_instance
  exact IsClosedImmersion.of_comp _ m

private theorem evaluate_lineCylinder (a : k) :
    Spec.map (CommRingCat.ofHom (evalRingHom (algebraMap k A a))) ≫ (e).hom.left =
      (nativeAffineSection (.of k) U a).left := by
  apply (cancel_mono (nativeParameterIso (.of k) U).hom).mp
  rw [nativeSection_parameterIso, Category.assoc]
  have hc : (e).hom.left ≫ (nativeParameterIso (.of k) U).hom =
      (ambientIso (algebraMap k A)).hom := by
    exact congrArg (fun f => f.left)
      (show (e).hom ≫ (affineCylinderPolynomialIso (.of k) U).hom =
        (linePolynomialProductIso (k := k) (R := A)).hom from by simp [lineCylinderIso])
  rw [hc]
  apply pullback.hom_ext
  · simp only [Category.assoc, endpoint_projection]
    change Spec.map (CommRingCat.ofHom (evalRingHom (algebraMap k A a))) ≫
        (ambientIso (algebraMap k A)).hom ≫
          pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A)))
            (polynomialProjection (.of k)) = 𝟙 (Spec (.of A))
    rw [ambientIso_fst, polynomialProjection, ← Spec.map_comp]
    have h : CommRingCat.ofHom (C : A →+* A[X]) ≫
        CommRingCat.ofHom (evalRingHom (algebraMap k A a)) = 𝟙 _ := by
      ext x
      exact eval_C
    rw [h, Spec.map_id]
  · simp only [Category.assoc, endpoint_snd]
    change Spec.map (CommRingCat.ofHom (evalRingHom (algebraMap k A a))) ≫
        (ambientIso (algebraMap k A)).hom ≫
          pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A)))
            (polynomialProjection (.of k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k A)) ≫
        Spec.map (CommRingCat.ofHom (evalRingHom a))
    have h : CommRingCat.ofHom (mapRingHom (algebraMap k A)) ≫
        CommRingCat.ofHom (evalRingHom (algebraMap k A a)) =
      CommRingCat.ofHom (evalRingHom a) ≫ CommRingCat.ofHom (algebraMap k A) := by
      apply CommRingCat.hom_ext
      apply Polynomial.ringHom_ext
      · intro b
        simp
      · simp
    rw [ambientIso_snd, ← Spec.map_comp, ← Spec.map_comp, h]

omit [Algebra k R] [Algebra.Smooth k R] [IsScalarTower k R A] [Algebra.Smooth k A] in
private theorem specialized_coefficients (a : k) :
    (evalRingHom (algebraMap k A a)).comp (parameterCoefficients (R := R) (A := A)) =
      algebraMap R A := by
  ext r
  exact eval_C

omit [Algebra k R] [Algebra.Smooth k R] [IsScalarTower k R A] [Algebra.Smooth k A] in
/-- The same original boundary remains invertible on the entire polynomial endpoint. -/
theorem polynomialFamily_endpoint_unit (p : A[X][X]) (f : R[X])
    (hf : IsUnit (AdjoinRoot.mk p (f.map (parameterCoefficients (R := R) (A := A)))))
    (a : k) :
    IsUnit (AdjoinRoot.mk (p.map (evalRingHom (algebraMap k A a))) (f.map (algebraMap R A))) := by
  simpa only [specialized_coefficients] using coefficient_boundary_unit
    (parameterCoefficients (R := R) (A := A)) (evalRingHom (algebraMap k A a)) p f hf

private def affinePolynomialFamily (p : A[X][X]) (hp : p.Monic) :
    Cor.mk (affineLineCylinder.obj U) ⟶ Cor.mk W := by
  obtain ⟨hfin, hflat⟩ := polynomialFamilySource_finite_flat (k := k) p hp
  exact Cor.ofFiniteFlatSpan (polynomialFamilySource (k := k) p)
    (target (parameterCoefficients (R := R) (A := A)) p)
    (polynomialFamily_affine_base (k := k) p)

private theorem openPolynomialFamily_comp_inclusion
    (p : A[X][X]) (hp : p.Monic) (f : R[X])
    (hf : IsUnit (AdjoinRoot.mk p (f.map (parameterCoefficients (R := R) (A := A))))) :
    openPolynomialFamily (k := k) p hp f hf ≫ (Cor.graphFunctor k).map (openInclusion f) =
      affinePolynomialFamily (k := k) (R := R) p hp := by
  obtain ⟨hfin, hflat⟩ := polynomialFamilySource_finite_flat (k := k) p hp
  erw [openPolynomialFamily, Cor.ofFiniteFlatSpan_comp_graph, affinePolynomialFamily]
  apply Cor.ofFiniteFlatSpan_eq_of_iso (Iso.refl _)
  · exact Category.id_comp _
  · exact (Category.id_comp _).trans (openTarget_inclusion _ _ _ _).symm

private theorem graph_affinePolynomialFamily (p : A[X][X]) (hp : p.Monic) (a : k) :
    (Cor.graphFunctor k).map (nativeAffineSection (.of k) U a) ≫
      affinePolynomialFamily (k := k) (R := R) p hp =
    affinePolynomialSpan (k := k) (R := R) (p.map (evalRingHom (algebraMap k A a))) (hp.map _) := by
  let φ := evalRingHom (algebraMap k A a)
  let σ := nativeAffineSection (.of k) U a
  let F := polynomialFamilySource (k := k) p
  let T := target (parameterCoefficients (R := R) (A := A)) p
  let m := pullback.lift F T (polynomialFamily_affine_base (k := k) p)
  let := source_finite p hp
  let := source_flat p hp
  let := source_finite (p.map φ) (hp.map φ)
  let := source_flat (p.map φ) (hp.map φ)
  let : IsIso (e).hom.left :=
    inferInstanceAs (IsIso ((Scheme.SmoothSite.forgetScheme _).mapIso e).hom)
  let : IsClosedImmersion m := polynomialFamily_pair_closed p
  let : IsFinite F := by dsimp only [F, polynomialFamilySource]; infer_instance
  let : Flat F := by dsimp only [F, polynomialFamilySource]; infer_instance
  let : IsFinite (m ≫ pullback.fst (affineLineCylinder.obj U).hom (W).hom) := by
    rw [show m ≫ pullback.fst _ _ = F from pullback.lift_fst _ _ _]
    infer_instance
  let : Flat (m ≫ pullback.fst (affineLineCylinder.obj U).hom (W).hom) := by
    rw [show m ≫ pullback.fst _ _ = F from pullback.lift_fst _ _ _]
    infer_instance
  erw [affinePolynomialFamily]
  have he := Cor.nativeSection_comp_ofFiniteFlatSpan_pair U W a m
  simp only [m, pullback.lift_fst, pullback.lift_snd] at he
  rw [he, affinePolynomialSpan]
  have Hiso : IsPullback (𝟙 (U).left) (Spec.map (CommRingCat.ofHom φ)) σ.left (e).hom.left := by
    apply IsPullback.of_horiz_isIso
    exact ⟨by simpa only [Category.id_comp] using (evaluate_lineCylinder (A := A) a).symm⟩
  have H : IsPullback (source (p.map φ)) (coefficientMap φ p) σ.left F := by
    have hh := (coefficient_isPullback φ p).paste_horiz Hiso
    have hid : source (p.map φ) ≫ 𝟙 (U).left = source (p.map φ) := Category.comp_id _
    change IsPullback (source (p.map φ) ≫ 𝟙 (U).left) (coefficientMap φ p) σ.left F at hh
    rw [hid] at hh
    exact hh
  let f₀ := m ≫ pullback.fst (affineLineCylinder.obj U).hom (W).hom
  have hf₀ : f₀ = F := pullback.lift_fst _ _ _
  have H' : IsPullback (source (p.map φ)) (coefficientMap φ p) σ.left f₀ :=
    Eq.mp (congrArg (fun g => IsPullback (source (p.map φ)) (coefficientMap φ p) σ.left g)
      hf₀.symm) H
  symm
  apply Cor.ofFiniteFlatSpan_eq_of_iso H'.isoPullback
  · exact H'.isoPullback_hom_fst
  · rw [← Category.assoc, H'.isoPullback_hom_snd, coefficient_target]
    rw [specialized_coefficients]

/-- Specializing the native cylinder gives the original whole polynomial quotient. -/
theorem graph_openPolynomialFamily (p : A[X][X]) (hp : p.Monic) (f : R[X])
    (hf : IsUnit (AdjoinRoot.mk p (f.map (parameterCoefficients (R := R) (A := A)))))
    (a : k) :
    (Cor.graphFunctor k).map (nativeAffineSection (.of k) U a) ≫ openPolynomialFamily p hp f hf =
      openPolynomialSpan (k := k) (p.map (evalRingHom (algebraMap k A a)))
        (hp.map _) f (polynomialFamily_endpoint_unit p f hf a) := by
  let : IsOpenImmersion (openInclusion (k := k) f).left :=
    inferInstanceAs (IsOpenImmersion (principalOpen f).ι)
  apply PolynomialCurveCycles.openGraph_injective k (openInclusion (k := k) f)
  dsimp only
  rw [Category.assoc, openPolynomialFamily_comp_inclusion, openPolynomialSpan_comp_inclusion]
  exact graph_affinePolynomialFamily (R := R) p hp a

end AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
