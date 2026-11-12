/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.RingTheory.KTheory.GTheory.Dedekind.PrimarySupport
public import Colib.RingTheory.KTheory.GTheory.Dedekind.ResidueAssembly
public import Colib.RingTheory.KTheory.GTheory.Dedekind.ResidueFieldAssembly

/-!
# Native Dedekind localization on the original boundary maps

The primary-coordinate boundaries below are the original finite-module
`connectingHom`, followed by the original primary-evaluation K-map. They detect
the generic localization image in each source degree `n + 1`, for `n ≥ 0`. In particular the
degree-two generic image is the intersection of their degree-one kernels.

Injectivity of the actual degree-one generic localization map is retained as
an explicit premise. It implies that the original supported degree-one map is
trivial and that the original degree-two boundary is onto. Point-primary
vanishing gives a separate conditional generic injectivity statement; no
finite-field vanishing theorem is assumed or asserted here.

The proved quotient-residue assembly turns this surjectivity into lifting of
arbitrary finite quotient-residue G₁ families. Their coordinates use the inverse
of the proved original quotient-residue-to-primary equivalence.

The canonical native `Ideal.ResidueField` comparison supplies residue-field
coordinates with the same kernels. Arbitrary finite native residue-field G₁
families lift through the original boundary to their original support assembly,
with that raw boundary equation and every coordinate specified together.

These are native finite-module statements. Identification with scheme maps or
local-DVR boundaries requires their actual comparison and boundary-naturality
squares, which are not supplied by this module.

## Implementation provenance

Adapted from `Quillen/GTheory/Dedekind/Localization.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The native finite modules, actual
localization kernel, canonical scalar restrictions and original normalized K-maps are retained.
The standard exact structures use Colib's native abelian structures directly.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.Abelian CategoryTheory.Abelian.Devissage
open FGModuleCat.PrimaryDecomposition
open scoped nonZeroDivisors DirectSum

namespace FGModuleCat.DedekindPrimary

attribute [local instance] Abelian.hasFiniteBiproducts

variable (R : Type u) [CommRing R] [IsDedekindDomain R]

/-- The original primary-evaluation K-maps jointly detect equality in the
actual native supported group, in every nonnegative degree. -/
theorem supportedK_ext (n : ℕ)
    {a b : FGModuleCat.Localization.SupportedG.{u, u} (nonZeroDivisors R) n}
    (h : ∀ p, (primaryEvaluationExactFunctor R p).KMap n a =
      (primaryEvaluationExactFunctor R p).KMap n b) : a = b := by
  apply (primaryKEquiv R n).injective
  apply CategoryTheory.Pi.FiniteSupport.evaluationK_ext (PrimaryCategory R) n
  intro p
  change (Pi.finiteCategoryEvaluation (PrimaryCategory R) p).KMap n
      ((nativePrimaryExactFunctor R).KMap n a) =
    (Pi.finiteCategoryEvaluation (PrimaryCategory R) p).KMap n
      ((nativePrimaryExactFunctor R).KMap n b)
  exact (DFunLike.congr_fun (ExactFunctor.KMap_comp (nativePrimaryExactFunctor R)
    (Pi.finiteCategoryEvaluation (PrimaryCategory R) p) n) a).symm.trans
      ((h p).trans (DFunLike.congr_fun
        (ExactFunctor.KMap_comp (nativePrimaryExactFunctor R)
          (Pi.finiteCategoryEvaluation (PrimaryCategory R) p) n) b))

/-- The actual supported class is the identity precisely when every original
primary evaluation is the identity. -/
theorem supported_eq_one_iff (n : ℕ)
    (a : FGModuleCat.Localization.SupportedG.{u, u} (nonZeroDivisors R) n) :
    a = 1 ↔ ∀ p, (primaryEvaluationExactFunctor R p).KMap n a = 1 := by
  constructor
  · rintro rfl p
    exact map_one _
  · intro h
    exact supportedK_ext R n (fun p => (h p).trans (map_one _).symm)

/-- The original boundary followed by the actual point-primary evaluation. -/
def primaryBoundary (n : ℕ) (p : IsDedekindDomain.HeightOneSpectrum R) :
    FGModuleCat.FractionLocalization.G.{u, u} (Localization (nonZeroDivisors R)) (n + 1) →*
      PrimaryK R p n :=
  ((primaryEvaluationExactFunctor R p).KMap n).comp
    (FGModuleCat.Localization.connectingHom.{u, u} (nonZeroDivisors R) n)

/-- Membership in the native generic localization image is detected by the
original point-primary boundary coordinates. -/
theorem mem_localization_range_iff_primaryBoundary_eq_one (n : ℕ)
    (a : FGModuleCat.FractionLocalization.G.{u, u} (Localization (nonZeroDivisors R)) (n + 1)) :
    a ∈ (FGModuleCat.Localization.localizationKMap.{u, u} (nonZeroDivisors R) (n + 1)).range ↔
      ∀ p, primaryBoundary R n p a = 1 := by
  rw [FGModuleCat.Localization.localization_range_eq_connecting_ker]
  exact supported_eq_one_iff R n _

/-- The actual generic localization image is the intersection of the kernels
of the actual primary-coordinate boundaries. -/
theorem localization_range_eq_iInf_primaryBoundary_ker (n : ℕ) :
    (FGModuleCat.Localization.localizationKMap.{u, u} (nonZeroDivisors R) (n + 1)).range =
      ⨅ p, (primaryBoundary R n p).ker := by
  ext a
  simpa only [Subgroup.mem_iInf, MonoidHom.mem_ker] using
    mem_localization_range_iff_primaryBoundary_eq_one R n a

/-- The native G₂ generic image is detected by all primary G₁ boundary coordinates. -/
theorem genericG2_range_eq_iInf_primaryBoundaryK1_ker :
    (FGModuleCat.Localization.localizationKMap.{u, u} (nonZeroDivisors R) 2).range =
      ⨅ p, (primaryBoundary R 1 p).ker :=
  localization_range_eq_iInf_primaryBoundary_ker R 1

/-- Generic injectivity in one degree forces the original supported inclusion
in that degree to be trivial. -/
theorem supportedKMap_eq_one_of_localization_injective (n : ℕ)
    (h : Function.Injective
      (FGModuleCat.Localization.localizationKMap.{u, u} (nonZeroDivisors R) n)) :
    FGModuleCat.Localization.supportedKMap.{u, u} (nonZeroDivisors R) n = 1 := by
  apply MonoidHom.range_eq_bot_iff.mp
  exact (FGModuleCat.Localization.supported_range_eq_localization_ker
    (nonZeroDivisors R) n).trans (MonoidHom.ker_eq_bot _ h)

/-- Under explicit generic injectivity, the original next-degree boundary
onto the actual supported group is surjective. -/
theorem connectingHom_surjective_of_localization_injective (n : ℕ)
    (h : Function.Injective
      (FGModuleCat.Localization.localizationKMap.{u, u} (nonZeroDivisors R) n)) :
    Function.Surjective (FGModuleCat.Localization.connectingHom.{u, u} (nonZeroDivisors R) n) := by
  apply MonoidHom.range_eq_top.mp
  rw [FGModuleCat.Localization.connecting_range_eq_supported_ker,
    supportedKMap_eq_one_of_localization_injective R n h]
  exact MonoidHom.ker_one

/-- Explicit native G₁ generic injectivity makes the original native G₂
boundary onto, without assuming residue-field vanishing. -/
theorem boundaryG2_surjective_of_genericG1_injective
    (h : Function.Injective
      (FGModuleCat.Localization.localizationKMap.{u, u} (nonZeroDivisors R) 1)) :
    Function.Surjective (FGModuleCat.Localization.connectingHom.{u, u} (nonZeroDivisors R) 1) :=
  connectingHom_surjective_of_localization_injective R 1 h

/-- If every actual point-primary group vanishes in one degree, so does the
native supported group in that degree. -/
theorem supportedK_subsingleton_of_primaryK_subsingleton (n : ℕ)
    (h : ∀ p, Subsingleton (PrimaryK R p n)) :
    Subsingleton (FGModuleCat.Localization.SupportedG.{u, u} (nonZeroDivisors R) n) := by
  constructor
  intro a b
  exact supportedK_ext R n (fun p => @Subsingleton.elim _ (h p) _ _)

/-- Point-primary vanishing implies injectivity of the actual generic
localization map in that same degree. -/
theorem localization_injective_of_primaryK_subsingleton (n : ℕ)
    (h : ∀ p, Subsingleton (PrimaryK R p n)) :
    Function.Injective
      (FGModuleCat.Localization.localizationKMap.{u, u} (nonZeroDivisors R) n) := by
  let : Subsingleton (FGModuleCat.Localization.SupportedG.{u, u} (nonZeroDivisors R) n) :=
    supportedK_subsingleton_of_primaryK_subsingleton R n h
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [← FGModuleCat.Localization.supported_range_eq_localization_ker]
  apply MonoidHom.range_eq_bot_iff.mpr
  apply MonoidHom.ext
  intro a
  change FGModuleCat.Localization.supportedKMap.{u, u} (nonZeroDivisors R) n a = 1
  rw [Subsingleton.elim a 1, map_one]

/-- The native G₂ generic map is injective under explicit point-primary K₂
vanishing. Finite residue fields alone are not used as a vanishing proof. -/
theorem genericG2_injective_of_primaryK2_subsingleton
    (h : ∀ p, Subsingleton (PrimaryK R p 2)) :
    Function.Injective (FGModuleCat.Localization.localizationKMap.{u, u} (nonZeroDivisors R) 2) :=
  localization_injective_of_primaryK_subsingleton R 2 h

end FGModuleCat.DedekindPrimary

namespace FGModuleCat.DedekindResidue

attribute [local instance] Abelian.hasFiniteBiproducts

variable (R : Type u) [CommRing R] [IsDedekindDomain R]

/-- The quotient-residue coordinate of the original native boundary, using
the inverse of the proved original residue-to-primary equivalence. -/
def quotientResidueBoundary (n : ℕ) (p : IsDedekindDomain.HeightOneSpectrum R) :
    FGModuleCat.FractionLocalization.G.{u, u} (Localization (nonZeroDivisors R)) (n + 1) →*
      QuotientResidueK R p n :=
  (residuePrimaryKEquiv R p n).symm.toMonoidHom.comp (DedekindPrimary.primaryBoundary R n p)

/-- The quotient-residue coordinate and the original primary coordinate have
exactly the same kernel. -/
theorem quotientResidueBoundary_ker (n : ℕ) (p : IsDedekindDomain.HeightOneSpectrum R) :
    (quotientResidueBoundary R n p).ker = (DedekindPrimary.primaryBoundary R n p).ker :=
  MonoidHom.ker_comp_of_injective _ _ (residuePrimaryKEquiv R p n).symm.injective

/-- The native generic image is also the intersection of the quotient-residue
coordinate kernels. This does not identify them with local-DVR boundaries. -/
theorem localization_range_eq_iInf_quotientResidueBoundary_ker (n : ℕ) :
    (FGModuleCat.Localization.localizationKMap.{u, u} (nonZeroDivisors R) (n + 1)).range =
      ⨅ p, (quotientResidueBoundary R n p).ker := by
  simpa only [quotientResidueBoundary_ker] using
    DedekindPrimary.localization_range_eq_iInf_primaryBoundary_ker R n

/-- Original primary evaluation of actual quotient-residue assembly is the
original residue-to-primary equivalence at that coordinate. -/
theorem primaryEvaluation_quotientResidueAssembly (n : ℕ)
    (a : ⨁ p, Additive (QuotientResidueK R p (n + 1)))
    (p : IsDedekindDomain.HeightOneSpectrum R) :
    (DedekindPrimary.primaryEvaluationExactFunctor R p).KMap (n + 1)
        (quotientResidueAssemblyKEquiv R n a).toMul =
      residuePrimaryKEquiv R p (n + 1) (a p).toMul := by
  have h : DedekindPrimary.primaryDecompositionKEquiv R n
      (quotientResidueAssemblyKEquiv R n a) = residuePrimaryDirectSumEquiv R n a := by
    change DedekindPrimary.primaryDecompositionKEquiv R n
        ((DedekindPrimary.primaryDecompositionKEquiv R n).symm
          (residuePrimaryDirectSumEquiv R n a)) = _
    exact AddEquiv.apply_symm_apply _ _
  have hp := congrArg (fun x => x p) h
  rw [DedekindPrimary.primaryDecompositionKEquiv_apply] at hp
  change Additive.ofMul ((DedekindPrimary.primaryEvaluationExactFunctor R p).KMap (n + 1)
      (quotientResidueAssemblyKEquiv R n a).toMul) =
    Additive.ofMul (residuePrimaryKEquiv R p (n + 1) (a p).toMul) at hp
  exact congrArg Additive.toMul hp

/-- Explicit generic injectivity lifts every finite quotient-residue family
through the original next-degree boundary to its actual support assembly. -/
theorem exists_connectingHom_eq_quotientResidueAssembly (n : ℕ)
    (h : Function.Injective
      (FGModuleCat.Localization.localizationKMap.{u, u} (nonZeroDivisors R) (n + 1)))
    (a : ⨁ p, Additive (QuotientResidueK R p (n + 1))) :
    ∃ b : FGModuleCat.FractionLocalization.G.{u, u} (Localization (nonZeroDivisors R)) (n + 2),
      Additive.ofMul (FGModuleCat.Localization.connectingHom.{u, u} (nonZeroDivisors R) (n + 1) b) =
        quotientResidueAssemblyKEquiv R n a := by
  obtain ⟨b, hb⟩ := DedekindPrimary.connectingHom_surjective_of_localization_injective
    R (n + 1) h (quotientResidueAssemblyKEquiv R n a).toMul
  exact ⟨b, congrArg Additive.ofMul hb⟩

/-- Every finite quotient-residue family occurs as the actual quotient-residue
coordinates of a native next-degree boundary, under explicit generic injectivity. -/
theorem exists_quotientResidueBoundary_eq (n : ℕ)
    (h : Function.Injective
      (FGModuleCat.Localization.localizationKMap.{u, u} (nonZeroDivisors R) (n + 1)))
    (a : ⨁ p, Additive (QuotientResidueK R p (n + 1))) :
    ∃ b : FGModuleCat.FractionLocalization.G.{u, u} (Localization (nonZeroDivisors R)) (n + 2),
      ∀ p, quotientResidueBoundary R (n + 1) p b = (a p).toMul := by
  obtain ⟨b, hb⟩ := exists_connectingHom_eq_quotientResidueAssembly R n h a
  refine ⟨b, fun p => ?_⟩
  change (residuePrimaryKEquiv R p (n + 1)).symm
    ((DedekindPrimary.primaryEvaluationExactFunctor R p).KMap (n + 1)
      (FGModuleCat.Localization.connectingHom.{u, u} (nonZeroDivisors R) (n + 1) b)) = _
  have hb' := congrArg Additive.toMul hb
  change FGModuleCat.Localization.connectingHom.{u, u} (nonZeroDivisors R) (n + 1) b =
    (quotientResidueAssemblyKEquiv R n a).toMul at hb'
  rw [hb', primaryEvaluation_quotientResidueAssembly, MulEquiv.symm_apply_apply]

/-- Native generic G₁ injectivity lifts any finite quotient-residue G₁ family
to an original native G₂ boundary, with all actual residue coordinates prescribed. -/
theorem quotientResidueG1_finite_family_lift
    (h : Function.Injective
      (FGModuleCat.Localization.localizationKMap.{u, u} (nonZeroDivisors R) 1))
    (a : ⨁ p, Additive (QuotientResidueK R p 1)) :
    ∃ b : FGModuleCat.FractionLocalization.G.{u, u} (Localization (nonZeroDivisors R)) 2,
      ∀ p, quotientResidueBoundary R 1 p b = (a p).toMul :=
  exists_quotientResidueBoundary_eq R 0 h a

/-- The native residue-field coordinate of the original boundary, retaining
the canonical pointwise scalar-restriction comparison. -/
def residueFieldBoundary (n : ℕ) (p : IsDedekindDomain.HeightOneSpectrum R) :
    FGModuleCat.FractionLocalization.G.{u, u} (Localization (nonZeroDivisors R)) (n + 1) →*
      ResidueFieldK R p n :=
  (residueFieldKEquiv R p n).symm.toMonoidHom.comp (quotientResidueBoundary R n p)

/-- The native residue-field and quotient-residue coordinates have the same kernel. -/
theorem residueFieldBoundary_ker (n : ℕ) (p : IsDedekindDomain.HeightOneSpectrum R) :
    (residueFieldBoundary R n p).ker = (quotientResidueBoundary R n p).ker :=
  MonoidHom.ker_comp_of_injective _ _ (residueFieldKEquiv R p n).symm.injective

/-- The actual native generic image is the intersection of the native
residue-field coordinate kernels, without a local-DVR boundary identification. -/
theorem localization_range_eq_iInf_residueFieldBoundary_ker (n : ℕ) :
    (FGModuleCat.Localization.localizationKMap.{u, u} (nonZeroDivisors R) (n + 1)).range =
      ⨅ p, (residueFieldBoundary R n p).ker := by
  simpa only [residueFieldBoundary_ker] using
    localization_range_eq_iInf_quotientResidueBoundary_ker R n

/-- The actual native G₂ generic image is detected by all native residue-field
G₁ coordinates of the original boundary. -/
theorem genericG2_range_eq_iInf_residueFieldBoundaryK1_ker :
    (FGModuleCat.Localization.localizationKMap.{u, u} (nonZeroDivisors R) 2).range =
      ⨅ p, (residueFieldBoundary R 1 p).ker :=
  localization_range_eq_iInf_residueFieldBoundary_ker R 1

/-- A raw original boundary equal to actual native residue-field assembly has
exactly the prescribed actual residue-field coordinates. -/
theorem residueFieldBoundary_eq_of_assembly (n : ℕ)
    (a : ⨁ p, Additive (ResidueFieldK R p (n + 1)))
    (b : FGModuleCat.FractionLocalization.G.{u, u} (Localization (nonZeroDivisors R)) (n + 2))
    (hb : Additive.ofMul
      (FGModuleCat.Localization.connectingHom.{u, u} (nonZeroDivisors R) (n + 1) b) =
        residueFieldAssemblyKEquiv R n a)
    (p : IsDedekindDomain.HeightOneSpectrum R) :
    residueFieldBoundary R (n + 1) p b = (a p).toMul := by
  have hb' := congrArg Additive.toMul hb
  change FGModuleCat.Localization.connectingHom.{u, u} (nonZeroDivisors R) (n + 1) b =
    (quotientResidueAssemblyKEquiv R n (residueFieldDirectSumEquiv R n a)).toMul at hb'
  change (residueFieldKEquiv R p (n + 1)).symm
    ((residuePrimaryKEquiv R p (n + 1)).symm
      ((DedekindPrimary.primaryEvaluationExactFunctor R p).KMap (n + 1)
        (FGModuleCat.Localization.connectingHom.{u, u} (nonZeroDivisors R) (n + 1) b))) = _
  rw [hb', primaryEvaluation_quotientResidueAssembly, MulEquiv.symm_apply_apply]
  change (residueFieldKEquiv R p (n + 1)).symm
    (residueFieldKEquiv R p (n + 1) (a p).toMul) = _
  exact MulEquiv.symm_apply_apply _ _

/-- Explicit generic injectivity lifts each finite native residue-field family
to its actual support assembly through the original next-degree boundary. -/
theorem exists_connectingHom_eq_residueFieldAssembly (n : ℕ)
    (h : Function.Injective
      (FGModuleCat.Localization.localizationKMap.{u, u} (nonZeroDivisors R) (n + 1)))
    (a : ⨁ p, Additive (ResidueFieldK R p (n + 1))) :
    ∃ b : FGModuleCat.FractionLocalization.G.{u, u} (Localization (nonZeroDivisors R)) (n + 2),
      Additive.ofMul (FGModuleCat.Localization.connectingHom.{u, u} (nonZeroDivisors R) (n + 1) b) =
        residueFieldAssemblyKEquiv R n a :=
  exists_connectingHom_eq_quotientResidueAssembly R n h (residueFieldDirectSumEquiv R n a)

/-- A finite native residue-field family lifts with both its raw original
boundary class and all original residue-field coordinates prescribed. -/
theorem exists_residueFieldBoundary_lift (n : ℕ)
    (h : Function.Injective
      (FGModuleCat.Localization.localizationKMap.{u, u} (nonZeroDivisors R) (n + 1)))
    (a : ⨁ p, Additive (ResidueFieldK R p (n + 1))) :
    ∃ b : FGModuleCat.FractionLocalization.G.{u, u} (Localization (nonZeroDivisors R)) (n + 2),
      Additive.ofMul (FGModuleCat.Localization.connectingHom.{u, u} (nonZeroDivisors R) (n + 1) b) =
        residueFieldAssemblyKEquiv R n a ∧
      ∀ p, residueFieldBoundary R (n + 1) p b = (a p).toMul := by
  obtain ⟨b, hb⟩ := exists_connectingHom_eq_residueFieldAssembly R n h a
  exact ⟨b, hb, residueFieldBoundary_eq_of_assembly R n a b hb⟩

/-- Under the explicit original generic G₁-injectivity premise, every finite
native residue-field G₁ family is realized by one original native G₂ boundary. -/
theorem residueFieldG1_finite_family_lift
    (h : Function.Injective
      (FGModuleCat.Localization.localizationKMap.{u, u} (nonZeroDivisors R) 1))
    (a : ⨁ p, Additive (ResidueFieldK R p 1)) :
    ∃ b : FGModuleCat.FractionLocalization.G.{u, u} (Localization (nonZeroDivisors R)) 2,
      Additive.ofMul (FGModuleCat.Localization.connectingHom.{u, u} (nonZeroDivisors R) 1 b) =
        residueFieldK1AssemblyEquiv R a ∧
      ∀ p, residueFieldBoundary R 1 p b = (a p).toMul :=
  exists_residueFieldBoundary_lift R 0 h a

attribute [colib_tag "COL-0604",
  colib_ref "WeibelKBook" "V, Sections 6.6–6.7.3" "comparison"
    "Dedekind localization context; the named original maps specify the implementation",
  colib_ref "quillen" "Quillen/GTheory/Dedekind/Localization.lean" "adaptation"
    "Original residue-coordinate localization and conditional finite-family lifting"]
  localization_range_eq_iInf_residueFieldBoundary_ker
  genericG2_range_eq_iInf_residueFieldBoundaryK1_ker
  exists_residueFieldBoundary_lift residueFieldG1_finite_family_lift

end FGModuleCat.DedekindResidue
