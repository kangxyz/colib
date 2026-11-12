/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleLimit

/-!
# An integral marked refinement of an original affine etale neighborhood

An arbitrary stage of the small etale-neighborhood model need not be integral. Its actual
clopen normal component containing the marking is affine and integral. Its canonical affine
presentation is another object of the original neighborhood category, with the original marking
and an exact refinement map. The native strict-henselization cone factors through this object.
No assertion that every object of a chosen small cofiltered model is integral is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
  {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ X.left)

/-- Every original etale neighborhood of a normal object is normal. -/
instance etaleNeighborhood_isNormal [IsNormal X.left] (A : EtaleNeighborhood X ξ) :
    IsNormal ((etaleNeighborhoodToSmooth X ξ).obj A).left :=
  isNormal_of_etale (etaleNeighborhoodHom X ξ A).left

/-- Every original affine etale neighborhood of a locally Noetherian object is Noetherian. -/
instance etaleNeighborhood_isNoetherian [IsLocallyNoetherian X.left]
    (A : EtaleNeighborhood X ξ) :
    IsNoetherian ((etaleNeighborhoodToSmooth X ξ).obj A).left := by
  have := LocallyOfFiniteType.isLocallyNoetherian (etaleNeighborhoodHom X ξ A).left
  exact ⟨⟩

set_option backward.isDefEq.respectTransparency false in
/-- The marked actual normal component gives an integral affine refinement in the original
neighborhood category. Its inclusion is retained through the displayed canonical affine
isomorphism, so already descended curve, root and frame data can simply be pulled back. -/
theorem exists_integral_etaleNeighborhood_refinement
    [IsNormal X.left] [IsLocallyNoetherian X.left] (A : EtaleNeighborhood X ξ) :
    let m := etaleNeighborhoodMark X ξ A
    let x := m (IsLocalRing.closedPoint Ω)
    ∃ (C : EtaleNeighborhood X ξ) (f : C ⟶ A),
      IsIntegral ((etaleNeighborhoodToSmooth X ξ).obj C).left ∧
      IsNoetherian ((etaleNeighborhoodToSmooth X ξ).obj C).left ∧
      IsOpenImmersion (((etaleNeighborhoodToSmooth X ξ).map f).left) ∧
      IsClosedImmersion (((etaleNeighborhoodToSmooth X ξ).map f).left) ∧
      ∃ e : ((etaleNeighborhoodToSmooth X ξ).obj C).left ≅
        (normalComponentOpen x).toScheme,
        ((etaleNeighborhoodToSmooth X ξ).map f).left = e.hom ≫
          (normalComponentOpen x).ι := by
  intro m x
  let a := (etaleNeighborhoodHom X ξ A).left
  let U := normalComponentOpen x
  have : IsAffine U.toScheme := isAffine_of_isAffineHom U.ι
  let e := U.toScheme.isoSpec
  let l := liftToNormalComponent m x (mem_normalComponentOpen x)
  have hl : l ≫ U.ι = m := liftToNormalComponent_ι m x _
  let g := e.inv ≫ U.ι
  have : Etale (g ≫ a) := inferInstance
  let C : EtaleNeighborhood X ξ := (etaleNeighborhoodFiber X ξ).elementsMk
    (AffineEtale.mk (g ≫ a)) (Over.homMk (l ≫ e.hom) (by
      change (l ≫ e.hom) ≫ (g ≫ a) = ξ
      simp only [g, Category.assoc, e.hom_inv_id_assoc]
      rw [← Category.assoc, hl]
      exact etaleNeighborhoodMark_hom X ξ A))
  have hg : etaleNeighborhoodMark X ξ C ≫ g = m := by
    change (l ≫ e.hom) ≫ (e.inv ≫ U.ι) = m
    simpa only [Category.assoc, e.hom_inv_id_assoc] using hl
  let f : C ⟶ A := etaleNeighborhoodHomMk X ξ g rfl hg
  have hf : ((etaleNeighborhoodToSmooth X ξ).map f).left = g :=
    etaleNeighborhoodHomMk_map_left X ξ (A := C) (B := A) g rfl hg
  have hi : IsIntegral ((etaleNeighborhoodToSmooth X ξ).obj C).left := by
    change IsIntegral (Spec Γ(U.toScheme, ⊤))
    exact IsIntegral.of_isIso e.hom
  refine ⟨C, f, hi, inferInstance, ?_, ?_, e.symm, hf⟩ <;> rw [hf] <;> infer_instance

/-- The actual original curve pulled back to an original etale neighborhood is normal. -/
instance etaleNeighborhood_pullback_isNormal {N : Scheme.{u}} [IsNormal N]
    (p : N ⟶ X.left) (A : EtaleNeighborhood X ξ) :
    IsNormal (pullback p (etaleNeighborhoodHom X ξ A).left) :=
  isNormal_of_etale (pullback.fst p (etaleNeighborhoodHom X ξ A).left)

/-- Properness over the original locally Noetherian base makes the same actual curve model
Noetherian, also for an integral refinement outside the chosen small cofiltered model. -/
instance etaleNeighborhood_pullback_isNoetherian [IsLocallyNoetherian X.left]
    {N : Scheme.{u}} (p : N ⟶ X.left) [IsProper p] (A : EtaleNeighborhood X ξ) :
    IsNoetherian (pullback p (etaleNeighborhoodHom X ξ A).left) := by
  have := LocallyOfFiniteType.isLocallyNoetherian
    (pullback.snd p (etaleNeighborhoodHom X ξ A).left)
  have : CompactSpace (pullback p (etaleNeighborhoodHom X ξ A).left : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace
      (pullback.snd p (etaleNeighborhoodHom X ξ A).left)
  exact ⟨⟩

/-- Integrality of an original affine neighborhood gives a domain on its exact native ring. -/
theorem isDomain_etaleNeighborhood_ring (A : EtaleNeighborhood X ξ)
    [IsIntegral ((etaleNeighborhoodToSmooth X ξ).obj A).left] :
    IsDomain A.obj.left.unop :=
  (affine_isIntegral_iff A.obj.left.unop).mp
    (inferInstanceAs (IsIntegral ((etaleNeighborhoodToSmooth X ξ).obj A).left))

/-- The original strict-henselization cone factors through any such integral refinement by its
original cone leg. The structure map and all existing stage data are unchanged under pullback. -/
theorem etaleNeighborhoodStrictHenselizationCone_refinement
    (B : BigEtaleSite.{u}) (hX : B.Contains X.left) (s : GeometricPoint X.left)
    {A C : EtaleNeighborhood X s.hom} (f : C ⟶ A) :
    (etaleNeighborhoodStrictHenselizationCone X B hX s).π.app C ≫
      ((etaleNeighborhoodToSmooth X s.hom).map f).left =
        (etaleNeighborhoodStrictHenselizationCone X B hX s).π.app A :=
  (etaleNeighborhoodStrictHenselizationCone X B hX s).w f

end AlgebraicGeometry.Scheme.SmoothSite
