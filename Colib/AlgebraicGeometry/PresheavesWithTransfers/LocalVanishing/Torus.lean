/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.LocalVanishing.Contraction
public import Mathlib.CategoryTheory.Sites.LocallyInjective
import Colib.AlgebraicGeometry.PresheavesWithTransfers.ContractionInvariance
import Colib.AlgebraicGeometry.PresheavesWithTransfers.LocalVanishing.Field
import Colib.AlgebraicGeometry.PresheavesWithTransfers.LocalVanishing.Laurent
import Colib.AlgebraicGeometry.Sites.Smooth.Cohomology.GenericOpen

/-!
# Local zeros on the whole torus cylinder

On a smooth affine integral base, a Nisnevich local zero on the actual
Laurent chart yields a zero after a principal localization of the base.
Integral-affine local vanishing then supplies zero neighborhoods on every
original smooth base.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite Polynomial

universe v u

namespace AlgebraicGeometry.PresheafWithTransfers

open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.SmoothSite
open _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
open _root_.Algebra.Smooth

attribute [local instance] away_smooth

variable {k : Type u} [Field k]

/-- A locally zero A¹-invariant coefficient on the original torus cylinder
vanishes after a principal localization of the original affine base. -/
theorem torus_affineLocalizationZero_of_locally_zero
    (P : PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant)
    (hLocal : ∀ (X : SmoothSite (Spec (.of k))) (s : P.sections (Cor.mk X)),
      Presheaf.equalizerSieve (F := (toPresheaf k).obj P) s 0 ∈
        nisnevichTopology (Spec (.of k)) X) :
    (torusSections P).AffineLocalizationZero := by
  intro R _ _ _ _ s
  let T := openSite (k := k) (Polynomial.X : R[X])
  let i := puncturedProductIso (k := k) (R := R)
  let : IsIntegral T.left := IsIntegral.of_isIso (laurentSchemeIso (R := R)).hom
  let v := transfer P ((Cor.graphFunctor k).map i.hom) s
  obtain ⟨W, hW, hz⟩ := SmoothSite.exists_generic_open_mem_covering_sieve T _ (hLocal T v)
  let a := (Cor.graphFunctor k).map (SmoothSite.openInclusion T W)
  change transfer P a v = transfer P a 0 at hz
  obtain ⟨r, hr, hzero⟩ := exists_base_shrink_of_neighborhood_zero P hP W
    ⟨genericPoint T.left, hW⟩ v (hz.trans (map_zero _))
  refine ⟨r, hr, ?_⟩
  let φ := IsScalarTower.toAlgHom k R (Localization.Away r)
  let f := affineMorphism φ
  let i' := puncturedProductIso (k := k) (R := Localization.Away r)
  change transfer P
    ((Cor.parameterProduct (multiplicativeGroupObject (Spec (.of k)))).map
      ((Cor.graphFunctor k).map f)) s = 0
  rw [Cor.parameterProduct_graph]
  change transfer P ((Cor.graphFunctor k).map (Contraction.torusCylinder.map f)) s = 0
  have he : transfer P ((Cor.graphFunctor k).map i'.hom)
      (transfer P ((Cor.graphFunctor k).map (Contraction.torusCylinder.map f)) s) = 0 := by
    rw [← ConcreteCategory.comp_apply, ← transfer_comp, ← Functor.map_comp,
      ← puncturedProductIso_naturality φ, Functor.map_comp, transfer_comp,
      ConcreteCategory.comp_apply]
    exact hzero
  let g := transfer P ((Cor.graphFunctor k).map i'.hom)
  exact (ConcreteCategory.bijective_of_isIso g).injective (he.trans (map_zero g.hom).symm)

/-- The original torus reindexing of a locally zero A¹-invariant transfer
presheaf is locally zero on the original smooth Nisnevich site. -/
theorem torus_zeroSieve_mem_of_locally_zero
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (hLocal : ∀ (X : SmoothSite (Spec (.of k))) (s : P.sections (Cor.mk X)),
      Presheaf.equalizerSieve (F := (toPresheaf k).obj P) s 0 ∈ nisnevichTopology (Spec (.of k)) X)
    (X : SmoothSite (Spec (.of k))) (s : (torusSections P).sections (Cor.mk X)) :
    Presheaf.equalizerSieve (F := (toPresheaf k).obj (torusSections P)) s 0 ∈
      nisnevichTopology (Spec (.of k)) X := by
  let Q := torusSections P
  have hQ : Q.IsA1Invariant :=
    withParameter_isA1Invariant P hP (multiplicativeGroupObject (Spec (.of k)))
  have hG : Q.HasGenericOpenZeros :=
    hasGenericOpenZeros_of_affineLocalizationZero _ (torus_affineLocalizationZero_of_locally_zero
      P hP hLocal)
  choose O _hO hx hz using fun x =>
    exists_zero_neighborhood_of_generic_open_zeros (integralAffineLocalZero_of_field k)
      Q hQ hG X s x
  let a (x : X.left) := SmoothSite.openInclusion X (O x)
  let (x : X.left) : IsOpenImmersion (a x).left := inferInstanceAs (IsOpenImmersion (O x).ι)
  apply SmoothSite.mem_nisnevichTopology_iff.mpr
  refine ⟨Presieve.ofArrows _ a, (SmoothSite.ofArrows_mem_nisnevichPrecoverage_iff a).mpr
    ⟨fun _ => inferInstance, fun x => ⟨x, ⟨x, hx x⟩, rfl, inferInstance⟩⟩, ?_⟩
  rw [Presieve.ofArrows_le_iff]
  intro x
  change Q.transfer ((Cor.graphFunctor k).map (a x)) s =
    Q.transfer ((Cor.graphFunctor k).map (a x)) 0
  rw [map_zero]
  exact hz x

end AlgebraicGeometry.PresheafWithTransfers
