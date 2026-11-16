module

public import Colib.AlgebraicGeometry.KTheory.SupportedMayerVietorisForget

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry

universe u

example {V X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace V]
    (j : V ⟶ X) [IsOpenImmersion j] (T Z : X.Opens) (hT : IsCompact (T : Set X))
    (hZ : IsCompact (Z : Set X)) (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T) :
    letI : QuasiSeparatedSpace V := j.isOpenEmbedding.quasiSeparatedSpace
    letI : CompactSpace T.toScheme := isCompact_iff_compactSpace.mp hT
    letI : CompactSpace (j ⁻¹ᵁ T).toScheme :=
      isCompact_iff_compactSpace.mp (j.isCompact_preimage hT)
    (perfectSupportedKMap Z.ι 0).comp
        (SupportedMayerVietoris.connectingHom j T Z hcover hZ 0) =
      (PerfectMayerVietoris.connectingHom j T hcover 0).comp
        (perfectSupportedKMap ((j ⁻¹ᵁ T).ι ⁻¹ᵁ (j ⁻¹ᵁ Z)).ι 1) := by
  letI : QuasiSeparatedSpace V := j.isOpenEmbedding.quasiSeparatedSpace
  letI : CompactSpace T.toScheme := isCompact_iff_compactSpace.mp hT
  letI : CompactSpace (j ⁻¹ᵁ T).toScheme :=
    isCompact_iff_compactSpace.mp (j.isCompact_preimage hT)
  exact SupportedMayerVietoris.connectingHom_forget j T Z hcover hZ 0

example {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j] (T Z : X.Opens)
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T) (n : ℕ)
    (x : PerfectSupportedK ((j ⁻¹ᵁ Z) ⊔ (j ⁻¹ᵁ T).ι.opensRange).ι n) :
    perfectSupportedUnionForgetKMap T.ι Z n
        ((SupportedMayerVietoris.fiberEquiv j T Z hcover n).symm x) =
      (perfectSupportedExcisionKEquiv j T hcover n).symm
        (perfectSupportedUnionForgetKMap (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z) n x) :=
  DFunLike.congr_fun (SupportedMayerVietoris.fiberEquiv_symm_comp_forget j T Z hcover n) x

example {V X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace V]
    [QuasiSeparatedSpace V] (j : V ⟶ X) [IsOpenImmersion j] (T Z : X.Opens)
    [CompactSpace T.toScheme] [CompactSpace (j ⁻¹ᵁ T).toScheme]
    (hZ : IsCompact (Z : Set X)) (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T) (n : ℕ)
    (x : PerfectSupportedK ((j ⁻¹ᵁ T).ι ⁻¹ᵁ (j ⁻¹ᵁ Z)).ι (n + 1))
    (hx : SupportedMayerVietoris.connectingHom j T Z hcover hZ n x = 1) :
    PerfectMayerVietoris.connectingHom j T hcover n
      (perfectSupportedKMap ((j ⁻¹ᵁ T).ι ⁻¹ᵁ (j ⁻¹ᵁ Z)).ι (n + 1) x) = 1 := by
  have h := DFunLike.congr_fun (SupportedMayerVietoris.connectingHom_forget j T Z hcover hZ n) x
  simp only [MonoidHom.comp_apply, hx, map_one] at h
  exact h.symm

#print axioms SupportedMayerVietoris.connectingHom_forget
#print axioms SupportedMayerVietoris.fiberEquiv_symm_comp_forget
