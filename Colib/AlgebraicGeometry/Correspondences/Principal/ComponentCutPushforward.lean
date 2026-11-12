/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Principal.FiniteCutPushforward
public import Colib.AlgebraicGeometry.Morphisms.QuasiFinite.Coheight

/-!
# Principal cuts on the actual finite integral-image map

The native integral component map is finite and dominant. Its generic degree
is the original map's degree at the original point, and its pointwise degrees
are those of the original map at the actual component inclusions. Quasi-finite
fibres supply codimension one without flatness.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

attribute [local instance] isIntegral_integralComponentAt

/-- The actual native map between integral point closures is finite. -/
instance isFinite_integralComponentMap {X Y : Scheme.{u}} (m : X ⟶ Y) [IsFinite m]
    (a : X) : IsFinite (integralComponentMap m a) := by
  have : IsFinite (integralComponentMap m a ≫
      (integralComponentAt (m a)).subschemeι) := by
    rw [integralComponentMap_subschemeι]
    infer_instance
  exact IsFinite.of_comp _ (integralComponentAt (m a)).subschemeι

/-- Pointwise residue degrees on the integral image use the original ambient
map and the original inclusion, not a replacement field extension. -/
theorem residueDegree_integralComponentMap_point {X Y : Scheme.{u}}
    (m : X ⟶ Y) (a : X) (x : (integralComponentAt a).subscheme) :
    (integralComponentMap m a).residueDegree x =
      m.residueDegree ((integralComponentAt a).subschemeι x) := by
  have H := congrArg (fun f : (integralComponentAt a).subscheme ⟶ Y => f.residueDegree x)
    (integralComponentMap_subschemeι m a)
  simpa only [residueDegree_comp, residueDegree_eq_one_of_isClosedImmersion,
    one_mul, mul_one] using H

/-- Every fibre of the actual finite integral-image map over codimension one
consists of codimension-one points. -/
theorem integralComponentMap_fiber_coheight {X Y : Scheme.{u}}
    (m : X ⟶ Y) [IsFinite m] (a : X)
    (y : (integralComponentAt (m a)).subscheme) (hy : Order.coheight y = 1)
    (x : (integralComponentAt a).subscheme) (hx : integralComponentMap m a x = y) :
    Order.coheight x = 1 :=
  (integralComponentMap m a).coheight_eq_one_of_locallyQuasiFinite x (hx ▸ hy)

/-- Full cuts on the actual integral image push forward with the original
generic and pointwise degrees. All source points over the same image are summed. -/
theorem integralComponentMap_principalCutLength {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (m : X ⟶ Y) [IsFinite m] (a : X)
    (s : Γ((integralComponentAt (m a)).subscheme, ⊤)) (hs : s ≠ 0)
    (y : (integralComponentAt (m a)).subscheme) (hy : Order.coheight y = 1) :
    (∑ᶠ x ∈ (integralComponentMap m a).base ⁻¹' {y},
      ((Module.length ((integralComponentAt a).subscheme.presheaf.stalk x)
        ((integralComponentAt a).subscheme.presheaf.stalk x ⧸ Ideal.span
          {(integralComponentAt a).subscheme.presheaf.germ ⊤ x (by trivial)
            ((integralComponentMap m a).appTop s)})).toNat : ℤ) *
              (m.residueDegree ((integralComponentAt a).subschemeι x) : ℤ)) =
      (m.residueDegree a : ℤ) *
        ((Module.length ((integralComponentAt (m a)).subscheme.presheaf.stalk y)
          ((integralComponentAt (m a)).subscheme.presheaf.stalk y ⧸ Ideal.span
            {(integralComponentAt (m a)).subscheme.presheaf.germ ⊤ y
              (by trivial) s})).toNat : ℤ) := by
  let : IsLocallyNoetherian (integralComponentAt a).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (integralComponentAt a).subschemeι
  let : IsLocallyNoetherian (integralComponentAt (m a)).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (integralComponentAt (m a)).subschemeι
  have H := finsum_principalCutLength_mul_residueDegree (integralComponentMap m a)
    s hs y hy (fun x hx => integralComponentMap_fiber_coheight m a y hy x hx)
  rw [residueDegree_integralComponentMap] at H
  simpa only [residueDegree_integralComponentMap_point] using H

/-- The generic integral closure inside an integral scheme is the whole scheme. -/
theorem isIso_genericComponentInclusion (X : Scheme.{u}) [IsIntegral X] :
    IsIso (integralComponentAt (genericPoint X)).subschemeι := by
  let : Surjective (integralComponentAt (genericPoint X)).subschemeι := ⟨by
    rw [← Set.range_eq_univ, Scheme.IdealSheafData.range_subschemeι,
      coe_support_integralComponentAt, genericPoint_spec X]⟩
  exact isIso_of_isClosedImmersion_of_surjective _

/-- The original integral source factors canonically through its native integral
image, without replacing its source by another component model. -/
def integralImageMap {X Y : Scheme.{u}} [IsIntegral X] (m : X ⟶ Y) :
    X ⟶ (integralComponentAt (m (genericPoint X))).subscheme := by
  let := isIso_genericComponentInclusion X
  exact inv (integralComponentAt (genericPoint X)).subschemeι ≫
    integralComponentMap m (genericPoint X)

/-- The canonical image factor retains the original map literally. -/
@[reassoc]
theorem integralImageMap_inclusion {X Y : Scheme.{u}} [IsIntegral X] (m : X ⟶ Y) :
    integralImageMap m ≫ (integralComponentAt (m (genericPoint X))).subschemeι = m := by
  let := isIso_genericComponentInclusion X
  simp only [integralImageMap, Category.assoc, integralComponentMap_subschemeι,
    IsIso.inv_hom_id_assoc]

/-- Finiteness of the original integral map descends to the canonical image factor. -/
instance integralImageMap_isFinite {X Y : Scheme.{u}} [IsIntegral X]
    (m : X ⟶ Y) [IsFinite m] : IsFinite (integralImageMap m) := by
  have : IsFinite (integralImageMap m ≫
      (integralComponentAt (m (genericPoint X))).subschemeι) := by
    rw [integralImageMap_inclusion]
    infer_instance
  exact IsFinite.of_comp _ (integralComponentAt (m (genericPoint X))).subschemeι

/-- The canonical image factor is dominant, without requiring the ambient map
to dominate its ambient target. -/
instance integralImageMap_isDominant {X Y : Scheme.{u}} [IsIntegral X]
    (m : X ⟶ Y) : IsDominant (integralImageMap m) := by
  apply ((tfae_isDominant_of_isIntegral (integralImageMap m)).out 1 2).mpr
  apply (integralComponentAt (m (genericPoint X))).subschemeι.isClosedEmbedding.injective
  change (integralImageMap m ≫
    (integralComponentAt (m (genericPoint X))).subschemeι) (genericPoint X) = _
  rw [integralImageMap_inclusion]
  exact (genericPointOf_integralComponentAt _).symm

/-- All original pointwise residue degrees survive the canonical image factor. -/
theorem integralImageMap_residueDegree {X Y : Scheme.{u}} [IsIntegral X]
    (m : X ⟶ Y) (x : X) : (integralImageMap m).residueDegree x = m.residueDegree x := by
  have H := congrArg (fun f : X ⟶ Y => f.residueDegree x) (integralImageMap_inclusion m)
  simpa only [residueDegree_comp, residueDegree_eq_one_of_isClosedImmersion, one_mul] using H

/-- The exact original integral source and its exact integral image satisfy the
full finite-cut formula with both original residue degrees and every image collision. -/
theorem integralImageMap_principalCutLength {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (m : X ⟶ Y) [IsFinite m]
    (s : Γ((integralComponentAt (m (genericPoint X))).subscheme, ⊤)) (hs : s ≠ 0)
    (y : (integralComponentAt (m (genericPoint X))).subscheme)
    (hy : Order.coheight y = 1) :
    (∑ᶠ x ∈ (integralImageMap m).base ⁻¹' {y},
      ((Module.length (X.presheaf.stalk x)
        (X.presheaf.stalk x ⧸ Ideal.span
          {X.presheaf.germ ⊤ x (by trivial) ((integralImageMap m).appTop s)})).toNat : ℤ) *
            (m.residueDegree x : ℤ)) =
      (m.residueDegree (genericPoint X) : ℤ) *
        ((Module.length
          ((integralComponentAt (m (genericPoint X))).subscheme.presheaf.stalk y)
          ((integralComponentAt (m (genericPoint X))).subscheme.presheaf.stalk y ⧸ Ideal.span
            {(integralComponentAt (m (genericPoint X))).subscheme.presheaf.germ ⊤ y
              (by trivial) s})).toNat : ℤ) := by
  let : IsLocallyNoetherian (integralComponentAt (m (genericPoint X))).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian
      (integralComponentAt (m (genericPoint X))).subschemeι
  have H := finsum_principalCutLength_mul_residueDegree (integralImageMap m) s hs y hy
    (fun x hx => (integralImageMap m).coheight_eq_one_of_locallyQuasiFinite x (hx ▸ hy))
  simpa only [integralImageMap_residueDegree] using H

end Stacks.Chow
