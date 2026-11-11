/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Additive.Ext
public import Colib.AlgebraicGeometry.Sites.Smooth.Torus
public import Colib.RingTheory.KTheory.MilnorK.Symbols.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.FieldNorm

/-!
# Milnor norm evaluation of finite point correspondences

The global functions on the native integral support form a finite field extension
of the base. Pulling back the forward Laurent unit along each torus coordinate
gives the tuple for the Milnor symbol in that field. The native finite field norm
evaluates the symbol in any characteristic. The native additive extension
retains the signed integer coefficient of each prime.

Adapted from `motivic_source_a6805c4`,
`Motivic/Cohomology/Diagonal/PointNorm.lean:41-142`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalPointNorm

open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]

/-- An admissible point in the actual ambient of the point-to-torus correspondence. -/
abbrev Generator (q : ℕ) :=
  {z : pullback (C := Scheme) (𝟙 (Spec (.of k))) (SmoothSite.torusPower (Spec (.of k)) q).hom //
    IsFiniteCorrespondencePoint (𝟙 (Spec (.of k)))
      (SmoothSite.torusPower (Spec (.of k)) q).hom z}

variable {k} {q : ℕ} (Z : Generator k q)

/-- The native integral closed support of an admissible point. -/
abbrev support : Scheme.{u} := (integralComponentAt Z.val).subscheme

instance supportIntegral : IsIntegral (support Z) := isIntegral_integralComponentAt Z.val

/-- The source projection of the actual support. -/
def projection : support Z ⟶ Spec (.of k) :=
  (integralComponentAt Z.val).subschemeι ≫ pullback.fst _ _

instance projectionFinite : IsFinite (projection Z) := Z.property.1

instance supportAffine : IsAffine (support Z) := isAffine_of_isAffineHom (projection Z)

/-- The target projection of the actual support. -/
def targetProjection : support Z ⟶ (SmoothSite.torusPower (Spec (.of k)) q).left :=
  (integralComponentAt Z.val).subschemeι ≫ pullback.snd _ _

/-- The ring of global functions of the whole support. -/
abbrev coordinateRing : CommRingCat.{u} := Γ(support Z, ⊤)

/-- The original support with its canonical global-section affine chart. -/
def supportIsoSpec : support Z ≅ Spec (coordinateRing Z) := (support Z).isoSpec

/-- The scalar map is pullback along the original source projection. -/
def scalarMap : k →+* coordinateRing Z :=
  (projection Z).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom

instance coordinateAlgebra : Algebra k (coordinateRing Z) := (scalarMap Z).toAlgebra

instance coordinateFinite : Module.Finite k (coordinateRing Z) := by
  change (scalarMap Z).Finite
  exact (projection Z).finite_appTop.comp
    (RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective)

/-- The integral finite support has a field of global functions. -/
theorem coordinateRing_isField : IsField (coordinateRing Z) :=
  isField_of_universallyClosed k (projection Z)

instance coordinateField : Field (coordinateRing Z) := (coordinateRing_isField Z).toField

/-- Pullback of the forward Laurent unit along the given original torus coordinate. -/
def coordinateUnit (i : Fin q) : (coordinateRing Z)ˣ :=
  Units.map ((targetProjection Z ≫
    (SmoothSite.torusCoordinate (Spec (.of k)) q i).left).appTop).hom.toMonoidHom
      (multiplicativeGroupBaseChangeCoordinate (Spec (.of k)))

/-- The canonical affine chart retains the original projection to the base field. -/
@[reassoc] theorem supportIsoSpec_inv_projection :
    (supportIsoSpec Z).inv ≫ projection Z =
      Spec.map (CommRingCat.ofHom (algebraMap k (coordinateRing Z))) := by
  change (support Z).isoSpec.inv ≫ projection Z = _
  rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

/-- The finite-extension norm of the full coordinate symbol in the actual support field. -/
def generatorValue : MilnorKTheory k q :=
  milnorKNorm k (coordinateRing Z) q (milnorKTupleSymbol (coordinateUnit Z))

/-- Additive evaluation on the native signed group of point correspondences. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/Diagonal/PointNorm.lean:104-123"
  "adaptation" "Finite field norm of the ordered support units on native signed cycles"]
def cycleValue (k : Type u) [Field k] (q : ℕ) :
    finiteCorrespondences (𝟙 (Spec (.of k))) (SmoothSite.torusPower (Spec (.of k)) q).hom →+
      MilnorKTheory k q :=
  liftFiniteCorrespondence _ _ fun z hz => generatorValue (⟨z, hz⟩ : Generator k q)

/-- A signed prime is evaluated with its original integer coefficient. -/
@[simp] theorem cycleValue_single
    (z : pullback (C := Scheme) (𝟙 (Spec (.of k)))
      (SmoothSite.torusPower (Spec (.of k)) q).hom)
    (hz : IsFiniteCorrespondencePoint (𝟙 (Spec (.of k)))
      (SmoothSite.torusPower (Spec (.of k)) q).hom z) (n : ℤ) :
    cycleValue k q (singleFiniteCorrespondence _ _ z hz n) =
      n • generatorValue (⟨z, hz⟩ : Generator k q) :=
  liftFiniteCorrespondence_single _ _ _ _ _ _

/-- The coefficient-one cycle evaluates by the norm from its actual support field. -/
theorem cycleValue_cycle :
    cycleValue k q (singleFiniteCorrespondence _ _ Z.val Z.property 1) = generatorValue Z := by
  rw [cycleValue_single, one_zsmul]

/-- An identity coordinate gives a zero symbol in the support field and hence zero norm. -/
theorem generatorValue_eq_zero_of_coordinate_one (i : Fin q)
    (hi : coordinateUnit Z i = 1) : generatorValue Z = 0 := by
  rw [generatorValue, milnorKTupleSymbol_eq_zero_of_eq_one (coordinateUnit Z) i hi, map_zero]

/-- A signed cycle evaluates to zero if every support point has an identity coordinate. -/
theorem cycleValue_eq_zero_of_identity_support
    (α : finiteCorrespondences (𝟙 (Spec (.of k))) (SmoothSite.torusPower (Spec (.of k)) q).hom)
    (hα : ∀ Z : Generator k q, α.val Z.val ≠ 0 → ∃ i : Fin q, coordinateUnit Z i = 1) :
    cycleValue k q α = 0 := by
  classical
  rw [finiteCorrespondence_eq_sum_signedSingles _ _ α, map_sum]
  apply Finset.sum_eq_zero
  intro z _
  have hz : α.val z.val ≠ 0 := by
    simpa only [Set.Finite.mem_toFinset, Function.locallyFinsuppWithin.support,
      Function.mem_support] using z.property
  obtain ⟨i, hi⟩ := hα ⟨z.val, α.property.2 z.val hz⟩ hz
  rw [cycleValue_single, generatorValue_eq_zero_of_coordinate_one _ i hi, smul_zero]

end AlgebraicGeometry.MotivicCohomology.DiagonalPointNorm
