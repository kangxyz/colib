/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ClosedFibreCohomologyRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperGeometricFibreStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.InjectiveAcyclicityCriterion

/-!
# Proper restriction over a strictly henselian local ring

Restriction to the closed fibre of a proper scheme over a strictly henselian local ring
is bijective on cohomology of sheaves killed by a positive integer. The map is the native
`etaleCohomologyRestrictionMap`, not a chosen equivalence between the cohomology groups.

The residue field is already separably closed, so the closed fibre is a geometric fibre
in the sense used by the pinned Stacks proper base change theorem. Proper base change
therefore shows that underlying abelian sheaves of injective `ZMod n`-module sheaves become
acyclic on the closed fibre. The native dimension-shifting criterion then establishes
bijectivity of the canonical restriction map.

The acyclicity argument adapts
`Stacks.EtaleCohomology.subsingleton_H_scalarExtension_toSheaf_of_injective` from
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/ProperBaseChange/SeparablyClosedFieldExtension.lean`
at Stacks revision `5ed82d14634e8d9576bb844c7bd4e3da66d450e7` to a strictly henselian base.

Rings and schemes have universe `u`, abelian sheaves have coefficient universe `u + 1`,
and `Ext` is computed in universe `u + 1`. No dimension, smoothness, or primality
condition is imposed. Invertibility of the annihilating integer is not needed here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.ZModSheaf

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] hasExt_sheaf_smallEtale_succ

local instance (priority := 2000) (Z : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  isGrothendieckAbelian_sheaf_smallEtale.{u, 0} Z

local instance {Z : Scheme.{u}}
    (p : GrothendieckTopology.Point.{u + 1} Z.smallEtaleTopology) :
    (p.sheafFiber (A := AddCommGrpCat.{u + 1})).Additive :=
  Functor.additive_of_preserves_binary_products _

variable (R : Type u) [CommRing R] [StrictlyHenselianLocalRing R]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]

/-- Proper base change makes the underlying abelian sheaf of an injective sheaf of
`ZMod n`-modules acyclic on the closed fibre over a strictly henselian local base. -/
@[colib_ref "axiom_stacks_5ed82d14"
  "AlgebraicGeometry/EtaleCohomology/ProperBaseChange/SeparablyClosedFieldExtension.lean:91-112"
  "adaptation" "Injective-module acyclicity at the separably closed residue field of a strictly henselian local base",
  colib_ref "axiom_stacks_5ed82d14"
    "AlgebraicGeometry/EtaleCohomology/ProperBaseChange/ProperGeometricFibreStalk.lean:41-58"
    "ingredient" "Unconditional proper base change at the residue-field geometric point"]
theorem subsingleton_H_closedFibre_toSheaf_of_injective {n : ℕ} (hn : 0 < n)
    (J : SheafOfModules.{u + 1} (zmodRingSheaf.{u + 1} X.smallEtaleTopology n))
    [Injective J] (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0}
      (closedFibreInclusion R f)).obj ((SheafOfModules.toSheaf _).obj J)) q) := by
  let G := (SheafOfModules.toSheaf _).obj J
  have hT := torsionSheafProperty_toSheaf_zmod.{u, 0} hn J
  have hR : IsZero (((etaleAbelianDirectImage.{u, 0} f).rightDerived q).obj G) :=
    IsZero.of_iso
      (isZero_homology_etaleAbelianDerivedDirectImage_single_toSheaf_of_injective.{u, 0}
        f n J q (by exact_mod_cast hq))
      (Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso
        (etaleAbelianDirectImage.{u, 0} f) (etaleAbelianDerivedDirectImage.{u, 0} f)
        (etaleAbelianDerivedDirectImageUnit.{u, 0} f)
        Stacks.DerivedFunctor.exists_quasiIso_isKInjective G q).symm
  let e := etaleAbelianSheafFiberRightDerivedDirectImageIsoOfIsProper f
    (residueFieldPoint R) G hT q
  have hS := (((pointSmallEtale (residueFieldPoint R)).ulift.{u + 1}).sheafFiber
    (A := AddCommGrpCat.{u + 1})).map_isZero hR
  exact AddCommGrpCat.isZero_iff_subsingleton.1 (hS.of_iso e.symm)

/-- The canonical restriction to the closed fibre of a proper scheme over a strictly
henselian local ring is bijective in every degree for sheaves killed by a positive integer. -/
@[colib_tag "COL-1030", stacks 095T
  "Consequence over a strictly henselian local base: canonical closed-fibre restriction is bijective for bounded-torsion abelian sheaves",
  colib_ref "axiom_stacks_5ed82d14"
    "AlgebraicGeometry/EtaleCohomology/ProperBaseChange/ClosedFibreCohomologyRestriction.lean:130-155"
    "ingredient" "Canonical restriction criterion with its injective-fibre acyclicity premise proved by proper base change"]
theorem bijective_etaleCohomologyRestrictionMap_closedFibre_of_strictlyHenselian
    {n : ℕ} (hn : 0 < n) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : (n : ℤ) • 𝟙 F = 0) :
    Function.Bijective
      (etaleCohomologyRestrictionMap.{u, 0, u + 1} (closedFibreInclusion R f) F q) := by
  apply bijective_etaleCohomologyRestrictionMap_closedFibre_of_injective R f n _ q F hF
  intro J hJ r hr
  let := hJ
  exact subsingleton_H_closedFibre_toSheaf_of_injective R f hn J r hr

end Stacks.EtaleCohomology
