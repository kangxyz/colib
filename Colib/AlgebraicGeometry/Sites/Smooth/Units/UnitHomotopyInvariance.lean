/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Simplex.AffineUnitProjection
public import Colib.AlgebraicGeometry.Sites.Smooth.Sheaves.IntegralAffineSheafIso
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Continuity
public import Colib.AlgebraicGeometry.Sites.Smooth.Units.Sheaf

/-!
# Actual Gm homotopy invariance on all smooth objects

The projection is first proved invertible on every affine smooth object using
native polynomial units over its reduced global-sections ring. The existing
integral-affine cover detects the isomorphism on the whole smooth site. No
Noetherian assertion about nonaffine global sections is used. Empty and
disconnected objects require no exceptional assumption.

Adapted from UnitHomotopyInvariance.lean at motivic revision
a6805c4a87cdfd7717dd7a94039246a167f15380. The integral-affine detection lemma
reuses the existing genuine cover rather than introducing another site.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

open Contraction

variable (k : Type u) [Field k]

/-- Genuine global units on the literal relative product with the n-simplex. -/
def simplexUnitsSheaf (n : ℕ) :
    Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1} :=
  ⟨(parameterProduct (_root_.AlgebraicSimplex.smoothSiteObj k n)).op ⋙
      largeUnitsPresheaf (Spec (.of k)),
    parameterProduct_op_comp_isSheaf _ _ (largeUnitsPresheaf_isSheaf _)⟩

/-- Pullback along the actual projection, as an ordinary Nisnevich sheaf map. -/
def unitsSimplexPullback (n : ℕ) :
    largeUnitsSheaf (Spec (.of k)) ⟶ simplexUnitsSheaf k n where
  hom :=
    { app X := (largeUnitsPresheaf (Spec (.of k))).map
        (productFst X.unop (_root_.AlgebraicSimplex.smoothSiteObj k n)).op
      naturality X Y f := by
        change (largeUnitsPresheaf _).map _ ≫ (largeUnitsPresheaf _).map _ =
          (largeUnitsPresheaf _).map _ ≫ (largeUnitsPresheaf _).map _
        rw [← Functor.map_comp, ← Functor.map_comp]
        congr 1
        apply Quiver.Hom.unop_inj
        exact (productMap_fst f.unop (𝟙 (_root_.AlgebraicSimplex.smoothSiteObj k n))).symm }

/-- Actual affine projection pullback on units is an isomorphism. -/
theorem isIso_unitsSimplexPullback_affine (n : ℕ)
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left] :
    IsIso ((unitsSimplexPullback k n).hom.app (op X)) := by
  let : AlgebraicGeometry.IsReduced X.left := isReduced_of_isNormal X.left
  have hi := _root_.AlgebraicSimplex.isIso_units_affineSchemeProjection
    (X := X.left) X.hom n
  have hf : IsIso (ringUnitsFunctor.map
      (pullback.fst X.hom (_root_.AlgebraicSimplex.structureMap k n)).appTop) := by
    rw [← pullbackSymmetry_hom_comp_snd X.hom (_root_.AlgebraicSimplex.structureMap k n),
      Scheme.Hom.comp_appTop, Functor.map_comp]
    infer_instance
  change IsIso (AddCommGrpCat.uliftFunctor.map (ringUnitsFunctor.map
    (pullback.fst X.hom (_root_.AlgebraicSimplex.structureMap k n)).appTop))
  infer_instance

/-- Gm is invariant under every actual algebraic simplex over any field,
on all smooth objects, including disconnected and empty ones. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/Units/UnitHomotopyInvariance.lean"
  "adaptation" "Actual units projection via polynomial units and affine descent"]
instance isIso_unitsSimplexPullback (n : ℕ) : IsIso (unitsSimplexPullback k n) :=
  isIso_of_integral_affine_app k _ (fun X _ _ =>
    isIso_unitsSimplexPullback_affine k n X)

end AlgebraicGeometry.Scheme.SmoothSite
