/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.RingTheory.KTheory.GTheory.Dedekind.Localization
public import Colib.RingTheory.KTheory.Quillen.Field.FiniteFieldGTwo

/-!
# Generic G₂ injectivity for Dedekind domains with finite residue fields

Finiteness of every actual residue field annihilates the native torsion-supported
G₂ group. Localization exactness then gives injectivity of the original generic
G₂ map. No injectivity hypothesis on generic G₁ is used or inferred.

Implementation provenance: the three ring-theoretic clauses of
`Quillen/GTheory/Dedekind/FiniteResidueLocalization.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Its separate coherent scheme
pullback conclusions are not asserted here.
-/

@[expose] public noncomputable section

universe u

open scoped nonZeroDivisors

namespace FGModuleCat.DedekindFiniteResidue

variable (R : Type u) [CommRing R] [IsDedekindDomain R]

/-- Finiteness of the actual native residue field makes the actual point-primary
K2 group trivial, through the original two residue comparison maps. -/
theorem primaryKTwo_subsingleton (p : IsDedekindDomain.HeightOneSpectrum R)
    [Finite p.asIdeal.ResidueField] : Subsingleton (FGModuleCat.DedekindPrimary.PrimaryK R p 2)
      := by
  let e := (FGModuleCat.DedekindResidue.residueFieldKEquiv R p 2).trans
    (FGModuleCat.DedekindResidue.residuePrimaryKEquiv R p 2)
  constructor
  intro a b
  apply e.symm.injective
  exact @Subsingleton.elim _ (Quillen.Field.finiteModuleGTwo_subsingleton p.asIdeal.ResidueField)
    _ _

/-- Arithmetic finiteness at every actual height-one residue field annihilates
the original native supported G2 group. -/
theorem supportedGTwo_subsingleton
    (hfinite : ∀ p : IsDedekindDomain.HeightOneSpectrum R, Finite p.asIdeal.ResidueField) :
    Subsingleton (FGModuleCat.Localization.SupportedG.{u, u} (nonZeroDivisors R) 2) := by
  apply FGModuleCat.DedekindPrimary.supportedK_subsingleton_of_primaryK_subsingleton R 2
  intro p
  let : Finite p.asIdeal.ResidueField := hfinite p
  exact primaryKTwo_subsingleton R p

/-- The original generic finite-module G2 localization map is injective when
all actual height-one residue fields are finite. -/
theorem genericGTwo_injective
    (hfinite : ∀ p : IsDedekindDomain.HeightOneSpectrum R, Finite p.asIdeal.ResidueField) :
    Function.Injective (FGModuleCat.Localization.localizationKMap.{u, u} (nonZeroDivisors R) 2)
      := by
  apply FGModuleCat.DedekindPrimary.genericG2_injective_of_primaryK2_subsingleton R
  intro p
  let : Finite p.asIdeal.ResidueField := hfinite p
  exact primaryKTwo_subsingleton R p

attribute [colib_tag "COL-0605",
  colib_ref "WeibelKBook" "V, Sections 6.6–6.7.3" "comparison"
    "Dedekind localization context; the named original maps specify the implementation",
  colib_ref "quillen" "Quillen/GTheory/Dedekind/FiniteResidueLocalization.lean" "adaptation"
    "Ring-theoretic supported G2 vanishing and generic G2 injectivity with finite residue fields"]
  primaryKTwo_subsingleton supportedGTwo_subsingleton genericGTwo_injective

end FGModuleCat.DedekindFiniteResidue
