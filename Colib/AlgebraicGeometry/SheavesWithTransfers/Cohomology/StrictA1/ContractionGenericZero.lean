/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.LocalVanishing.Contraction
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.LocalVanishing.Laurent
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.Basic

/-!
# Generic open zeros of positive cohomology contractions

A positive ordinary cohomology class vanishes on an actual generic open
of the Laurent cylinder. Affine-line invariance in that degree moves the
zero to the whole cylinder after one principal base localization.

Adapted from `Motivic/Cohomology/Sheaf/LaurentGenericZero.lean`,
`Motivic/Cohomology/Sheaf/TorusModelZero.lean`, and
`Motivic/Cohomology/Sheaf/TorusModelGerm.lean` at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite Polynomial
open _root_.Stacks.Cohomology.FreeYonedaUnivLE
open _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite

universe w u

namespace AlgebraicGeometry.SheafCohomology

open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.SmoothSite
open PresheafWithTransfers
open _root_.Algebra.Smooth

attribute [local instance] away_smooth

variable {k : Type u} [Field k]
  [HasExt.{w} (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Positive cohomology on the native torus cylinder becomes zero after a
principal localization of the original smooth affine domain. -/
theorem torus_affineLocalizationZero_succ
    (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    (hP : (withTransfers k F (n + 1)).IsA1Invariant) :
    (torusSections (withTransfers k F (n + 1))).AffineLocalizationZero := by
  intro R _ _ _ _ s
  let P := withTransfers k F (n + 1)
  let T := openSite (k := k) (Polynomial.X : R[X])
  let i := puncturedProductIso (k := k) (R := R)
  let : IsIntegral T.left := IsIntegral.of_isIso (laurentSchemeIso (R := R)).hom
  let v := transfer P ((Cor.graphFunctor k).map i.hom) s
  obtain ⟨W, hW, hz⟩ := exists_generic_open_restriction_eq_zero
    ((SheafWithTransfers.toSheaf k).obj F) n T v
  have hv : transfer P ((Cor.graphFunctor k).map (SmoothSite.openInclusion T W)) v = 0 :=
    (withTransfers_graph k F (n + 1) (SmoothSite.openInclusion T W) v).trans hz
  obtain ⟨r, hr, hzero⟩ := exists_base_shrink_of_neighborhood_zero P hP W
    ⟨genericPoint T.left, hW⟩ v hv
  refine ⟨r, hr, ?_⟩
  let φ := IsScalarTower.toAlgHom k R (Localization.Away r)
  let f := affineMorphism φ
  let i' := puncturedProductIso (k := k) (R := Localization.Away r)
  change transfer P
    ((Cor.parameterProduct (multiplicativeGroupObject (Spec (.of k)))).map
      ((Cor.graphFunctor k).map f)) s = 0
  rw [Cor.parameterProduct_graph]
  have hmap : SmoothSite.productMap f (𝟙 (multiplicativeGroupObject (Spec (.of k)))) =
      Contraction.torusCylinder.map f := rfl
  rw [hmap]
  have he : transfer P ((Cor.graphFunctor k).map i'.hom)
      (transfer P ((Cor.graphFunctor k).map (Contraction.torusCylinder.map f)) s) = 0 := by
    rw [← ConcreteCategory.comp_apply, ← transfer_comp, ← Functor.map_comp]
    rw [show i'.hom ≫ Contraction.torusCylinder.map f = puncturedBaseMap φ ≫ i.hom
      from (puncturedProductIso_naturality φ).symm]
    rw [Functor.map_comp, transfer_comp, ConcreteCategory.comp_apply]
    exact hzero
  let g := transfer P ((Cor.graphFunctor k).map i'.hom)
  have hg₀ : g 0 = 0 := map_zero g.hom
  exact (ConcreteCategory.bijective_of_isIso g).injective (he.trans hg₀.symm)

/-- Each original positive contraction section has an actual generic open zero. -/
theorem contraction_hasGenericOpenZeros_succ
    (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    (hP : (withTransfers k F (n + 1)).IsA1Invariant) :
    (contraction (withTransfers k F (n + 1))).HasGenericOpenZeros :=
  hasGenericOpenZeros_of_affineLocalizationZero _
    (contraction_affineLocalizationZero _ (torus_affineLocalizationZero_succ F n hP))

end AlgebraicGeometry.SheafCohomology
