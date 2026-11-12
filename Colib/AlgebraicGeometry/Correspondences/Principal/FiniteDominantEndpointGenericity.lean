/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Morphisms.QuasiFinite.GenericFiber
public import Colib.Util.References
public import Colib.RingTheory.Spectrum.Prime.GoingDown
public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.RingTheory.Polynomial.Ideal
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Generic points of full evaluation fibres over a normal base

Going down over the original normal base places every generic point of the full
scheme-theoretic evaluation fibre over the original base generic point. Neither
normality nor flatness of the finite integral source is assumed. The affine
coordinates are the canonical global-Spec coordinates of the original map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped Polynomial

universe u

namespace AlgebraicGeometry.Scheme.FiniteDominantFace

section Coordinates

variable {A S : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [CommRing S] [IsDomain S]
  (φ : A[X] →+* S) (hφ : Function.Injective φ) (hfinite : φ.Finite)
  {E : Scheme.{u}} (e : E ⟶ Spec (.of S)) (b : E ⟶ Spec (.of A)) (a : A)
  (hsq : IsPullback e b (Spec.map (CommRingCat.ofHom φ))
    (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))))

include hsq

omit [IsDomain A] [IsIntegrallyClosed A] [IsDomain S] in
/-- The full original endpoint has exactly the support of the extended face
ideal. No reduced replacement or independently assumed kernel is used. -/
theorem mem_range_face_iff (s : Spec (.of S)) :
    s ∈ Set.range e ↔
      (Ideal.span {Polynomial.X - Polynomial.C a}).map φ ≤ s.asIdeal := by
  have hr : Set.range e = (Spec.map (CommRingCat.ofHom φ)) ⁻¹'
      Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨b x, (congrArg (fun f : E ⟶ Spec (.of A[X]) => f x) hsq.w).symm⟩
    · rintro ⟨y, hy⟩
      obtain ⟨x, hx, -⟩ := Scheme.exists_preimage_of_isPullback hsq z y hy.symm
      exact ⟨x, hx⟩
  rw [hr]
  change PrimeSpectrum.comap φ s ∈
    Set.range (PrimeSpectrum.comap (Polynomial.evalRingHom a)) ↔ _
  rw [range_comap_of_surjective _ _ (Polynomial.eval_surjective a)]
  change RingHom.ker (Polynomial.evalRingHom a) ≤ s.asIdeal.comap φ ↔ _
  rw [Polynomial.ker_evalRingHom, Ideal.map_le_iff_le_comap]

omit [IsDomain A] [IsIntegrallyClosed A] [IsDomain S] in
/-- An actual generic point of the unreduced endpoint gives a minimal prime
of its original extended evaluation ideal. -/
theorem face_generic_mem_minimalPrimes (x : E) (hx : x ∈ genericPoints E) :
    (e x).asIdeal ∈ ((Ideal.span {Polynomial.X - Polynomial.C a}).map φ).minimalPrimes := by
  let : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))) :=
    IsClosedImmersion.spec_of_surjective _ (Polynomial.eval_surjective a)
  let : IsClosedImmersion e := MorphismProperty.of_isPullback hsq.flip inferInstance
  refine ⟨⟨(e x).isPrime, (mem_range_face_iff φ e b a hsq (e x)).mp ⟨x, rfl⟩⟩, ?_⟩
  intro Q hQ hQx
  obtain ⟨y, hy⟩ := (mem_range_face_iff φ e b a hsq ⟨Q, hQ.1⟩).mpr hQ.2
  have hspec : e y ⤳ e x := by
    rw [hy]
    exact (PrimeSpectrum.le_iff_specializes _ _).mp hQx
  have hyx : y ⤳ x := e.isEmbedding.isInducing.specializes_iff.mp hspec
  have hxy : x ⤳ y := specializes_iff_closure_subset.mpr
    (hx.2 isIrreducible_singleton.closure hyx.closure_subset)
  have heq : y = x := (hyx.antisymm hxy).eq
  subst y
  exact le_of_eq (congrArg PrimeSpectrum.asIdeal hy)

include hφ hfinite

/-- The original face point lies over the exact zero prime of the original base. -/
theorem face_point_over_zero (x : E)
    (hx : (e x).asIdeal ∈ ((Ideal.span {Polynomial.X - Polynomial.C a}).map φ).minimalPrimes) :
    b x = (⊥ : PrimeSpectrum A) := by
  have : (Ideal.span {Polynomial.X - Polynomial.C a} : Ideal A[X]).IsPrime := by
    rw [← Polynomial.ker_evalRingHom]
    exact RingHom.ker_isPrime (Polynomial.evalRingHom a)
  have hcontract := Ideal.comap_eq_of_mem_minimalPrimes_map_prime φ hφ hfinite
    (Ideal.span {Polynomial.X - Polynomial.C a}) (e x).asIdeal hx
  have hpoint : (Spec.map (CommRingCat.ofHom φ)) (e x) =
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))) (b x) :=
    congrArg (fun f : E ⟶ Spec (.of A[X]) => f x) hsq.w
  have hconstants := congrArg
    (fun z : Spec (.of A[X]) => z.asIdeal.comap (Polynomial.C : A →+* A[X])) hpoint
  change ((e x).asIdeal.comap φ).comap Polynomial.C =
    ((b x).asIdeal.comap (Polynomial.evalRingHom a)).comap Polynomial.C
      at hconstants
  rw [hcontract, ← Polynomial.ker_evalRingHom, RingHom.comap_ker] at hconstants
  have heval : (Polynomial.evalRingHom a).comp (Polynomial.C : A →+* A[X]) =
      RingHom.id A := by ext b; simp
  have hid : RingHom.ker (RingHom.id A) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp Function.injective_id
  rw [heval, hid, Ideal.comap_comap, heval, Ideal.comap_id] at hconstants
  exact PrimeSpectrum.ext hconstants.symm

/-- Generic points of the full original evaluation fibre lie over the base generic point. -/
theorem face_generic_over_zero (x : E) (hx : x ∈ genericPoints E) :
    b x = (⊥ : PrimeSpectrum A) := by
  exact face_point_over_zero φ hφ hfinite e b a hsq x
    (face_generic_mem_minimalPrimes φ e b a hsq x hx)

end Coordinates

section OriginalMap

variable {A : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  {C : Scheme.{u}} [IsIntegral C]
  (f : C ⟶ Spec (.of A[X])) [IsFinite f] [IsDominant f]

/-- The original global coordinate map, with the canonical Spec comparison. -/
def coordinateMap : A[X] →+* Γ(C, ⊤) :=
  f.appTop.hom.comp (Scheme.ΓSpecIso (.of A[X])).inv.hom


omit [IsDomain A] [IsIntegrallyClosed A] [IsIntegral C] [IsFinite f] [IsDominant f] in
/-- The coordinate map is the literal original morphism under its canonical
Spec comparison, not an independently chosen affine presentation. -/
theorem coordinateMap_spec_eq [IsAffine C] :
    Spec.map (CommRingCat.ofHom (coordinateMap f)) = C.isoSpec.inv ≫ f := by
  rw [← Scheme.isoSpec_inv_naturality f, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

/-- Every generic point of an actual evaluation endpoint of the original
finite dominant integral support lies over the generic point of its base. -/
theorem original_face_generic_over_zero
    {E : Scheme.{u}} (e : E ⟶ C) (b : E ⟶ Spec (.of A)) (a : A)
    (hsq : IsPullback e b f
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))))
    (x : E) (hx : x ∈ genericPoints E) : b x = (⊥ : PrimeSpectrum A) := by
  let : IsAffine C := isAffine_of_isAffineHom f
  let : Nonempty (⊤ : C.Opens) :=
    ⟨⟨genericPoint C, TopologicalSpace.Opens.mem_top (genericPoint C)⟩⟩
  let : IsDomain Γ(C, ⊤) := IsIntegral.component_integral ⊤
  let φ := coordinateMap f
  have hfinite : φ.Finite :=
    f.finite_appTop.comp (RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso (.of A[X])).commRingCatIsoToRingEquiv.symm.surjective)
  have hinj : Function.Injective φ := by
    let : IsSchemeTheoreticallyDominant f := .of_isDominant f
    have hf : Function.Injective f.appTop := by
      intro x y h
      exact f.app_injective ⊤ h
    exact hf.comp (Scheme.ΓSpecIso (.of A[X])).commRingCatIsoToRingEquiv.symm.injective
  have hcoord : IsPullback C.isoSpec.hom f
      (Spec.map (CommRingCat.ofHom φ)) (𝟙 (Spec (.of A[X]))) :=
    IsPullback.of_horiz_isIso ⟨by rw [coordinateMap_spec_eq]; simp⟩
  have hface : IsPullback (e ≫ C.isoSpec.hom) b
      (Spec.map (CommRingCat.ofHom φ))
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))) := by
    simpa only [Category.comp_id] using hsq.paste_horiz hcoord
  exact face_generic_over_zero φ hinj hfinite (e ≫ C.isoSpec.hom) b a hface x hx


/-- The original endpoint map into a finite target endpoint sends every
component generic point to a component generic point. All coordinate and
minimal-prime data have been constructed from the original support map. -/
@[colib_tag "COL-1081"]
theorem original_face_generic_image_generic
    {E F : Scheme.{u}} (e : E ⟶ C) (b : E ⟶ Spec (.of A)) (a : A)
    (hsq : IsPullback e b f
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))))
    (q : F ⟶ Spec (.of A)) [IsFinite q] (r : E ⟶ F) (hr : r ≫ q = b)
    (x : E) (hx : x ∈ genericPoints E) : r x ∈ genericPoints F := by
  apply _root_.AlgebraicGeometry.Scheme.Hom.mem_genericPoints_of_image_generic q (r x)
  have hzero : q (r x) = (⊥ : PrimeSpectrum A) := by
    rw [← Scheme.Hom.comp_apply, hr]
    exact original_face_generic_over_zero f e b a hsq x hx
  rw [hzero]
  refine ⟨isIrreducible_singleton.closure, ?_⟩
  intro s _ _
  have H : closure ({(⊥ : PrimeSpectrum A)} : Set (PrimeSpectrum A)) = Set.univ :=
    (PrimeSpectrum.closure_singleton _).trans PrimeSpectrum.zeroLocus_bot
  exact H.symm ▸ Set.subset_univ s


end OriginalMap

end AlgebraicGeometry.Scheme.FiniteDominantFace
