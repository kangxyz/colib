/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteResidueDegree

/-!
# Actual image-stalk residue degrees through the canonical affine identification

The full remaining finite algebra acts through the inverse of the actual
`Scheme.ΓSpecIso`, followed by the structure morphism's global-section map.
Its source prime is the actual section-germ preimage of the maximal ideal at
an original point of the full model. We prove that its contraction is literally
the image point's prime in the actual image-stalk ring.

The residue degree for this canonical algebra action is the residue degree of
the original exterior finite morphism at the projected original point. The
transport uses native `Ideal.residueFieldRingEquiv`, its compatibility through
`Ideal.ResidueField.map_algebraMap`, and `Algebra.finrank_eq_of_equiv_equiv`.
No alternate residue field, ring action, or prime label is introduced.

This is a native-source application, not a new generic transport provider.
The comparison is pointwise for every model point over an arbitrary base.
No perfectness, reducedness, integrality, flatness of the finite map, choice of
a single component, or hypothetical coefficient comparison is assumed. Minimal
prime reindexing, Tor coefficient identification, and associativity are separate.

## References

* Stacks Project, Tag 02R4: finite pushforward uses the actual residue degree.
* Pinned Mathlib `RingTheory/LocalRing/ResidueField/Ideal.lean`:
  `Ideal.residueFieldRingEquiv`, `Ideal.ResidueField.map_algebraMap`, and
  `Ideal.ResidueField.ringHom_ext`.
* Pinned Mathlib `LinearAlgebra/Dimension/Finrank.lean`:
  `Algebra.finrank_eq_of_equiv_equiv`.
* Pinned Mathlib `AlgebraicGeometry/GammaSpecAdjunction.lean`:
  `toSpecΓ_SpecMap_ΓSpecIso_inv` identifies the literal contracted prime.
* Pinned Stacks `AlgebraicGeometry/Spaces/ElementaryChartFibre.lean`:
  `Scheme.comap_germ_maximalIdeal_eq_comap_appTop` and the existing affine
  residue-degree comparison, consumed through `RemainingFiniteResidueDegree`.

Validation status: source-only candidate, pending parent-run native checks.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- Under the actual algebra action, the source germ prime contracts to exactly
its actual image point's prime, with no relabeling through an unspecified equivalence. -/
theorem correspondenceRemainingFiniteGermPrime_comap_algebraMap
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (q : correspondenceRemainingFiniteModel f g h i z w v x) :
    letI := correspondenceRemainingFiniteAlgebra f g h i z w v x
    (Ideal.comap
      ((correspondenceRemainingFiniteModel f g h i z w v x).presheaf.germ ⊤ q trivial).hom
      (IsLocalRing.maximalIdeal
        ((correspondenceRemainingFiniteModel f g h i z w v x).presheaf.stalk q))).comap
      (algebraMap (correspondenceRemainingImageStalk f g h i z w v x)
        (correspondenceRemainingFiniteRing f g h i z w v x)) =
      (correspondenceRemainingFiniteModelStructure f g h i z w v x q).asIdeal := by
  letI := correspondenceRemainingFiniteAlgebra f g h i z w v x
  let R := correspondenceRemainingImageStalk f g h i z w v x
  let π := correspondenceRemainingFiniteModelStructure f g h i z w v x
  let Q := Ideal.comap
    ((correspondenceRemainingFiniteModel f g h i z w v x).presheaf.germ ⊤ q trivial).hom
    (IsLocalRing.maximalIdeal
      ((correspondenceRemainingFiniteModel f g h i z w v x).presheaf.stalk q))
  let P := Ideal.comap ((Spec R).presheaf.germ ⊤ (π q) trivial).hom
    (IsLocalRing.maximalIdeal ((Spec R).presheaf.stalk (π q)))
  have hP : P = Q.comap π.appTop.hom :=
    Scheme.comap_germ_maximalIdeal_eq_comap_appTop π q
  have hpoint : P.comap (Scheme.ΓSpecIso R).inv.hom = (π q).asIdeal := by
    have htriangle := congrArg (fun r : Spec R ⟶ Spec R => (r (π q)).asIdeal)
      (toSpecΓ_SpecMap_ΓSpecIso_inv R)
    exact htriangle
  rw [correspondenceRemainingFiniteAlgebra_algebraMap]
  change Q.comap (π.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom) = (π q).asIdeal
  rw [← Ideal.comap_comap, ← hP]
  exact hpoint

/-- The residue degree for the actual image-stalk algebra, at the literal contracted
source germ prime, is the original full exterior map's degree at the original label. -/
@[stacks 02R4 "the canonical full finite algebra retains the original finite-map residue degree"]
theorem primeResidueDegree_correspondenceRemainingFiniteAlgebra [IsSeparated h]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (q : correspondenceRemainingFiniteModel f g h i z w v x) :
    letI := correspondenceRemainingFiniteAlgebra f g h i z w v x
    Stacks.Length.primeResidueDegree
      (algebraMap (correspondenceRemainingImageStalk f g h i z w v x)
        (correspondenceRemainingFiniteRing f g h i z w v x))
      ((Ideal.comap
        ((correspondenceRemainingFiniteModel f g h i z w v x).presheaf.germ ⊤ q trivial).hom
        (IsLocalRing.maximalIdeal
          ((correspondenceRemainingFiniteModel f g h i z w v x).presheaf.stalk q))).comap
        (algebraMap (correspondenceRemainingImageStalk f g h i z w v x)
          (correspondenceRemainingFiniteRing f g h i z w v x)))
      (Ideal.comap
        ((correspondenceRemainingFiniteModel f g h i z w v x).presheaf.germ ⊤ q trivial).hom
        (IsLocalRing.maximalIdeal
          ((correspondenceRemainingFiniteModel f g h i z w v x).presheaf.stalk q))) =
      (correspondenceLeftIntermediateImageMap f g h i z w v).residueDegree
        (correspondenceRemainingFiniteModelProjection f g h i z w v x q) := by
  letI := correspondenceRemainingFiniteAlgebra f g h i z w v x
  let R := correspondenceRemainingImageStalk f g h i z w v x
  let B := correspondenceRemainingFiniteRing f g h i z w v x
  let π := correspondenceRemainingFiniteModelStructure f g h i z w v x
  let Q : Ideal B := Ideal.comap
    ((correspondenceRemainingFiniteModel f g h i z w v x).presheaf.germ ⊤ q trivial).hom
    (IsLocalRing.maximalIdeal
      ((correspondenceRemainingFiniteModel f g h i z w v x).presheaf.stalk q))
  let P := Ideal.comap ((Spec R).presheaf.germ ⊤ (π q) trivial).hom
    (IsLocalRing.maximalIdeal ((Spec R).presheaf.stalk (π q)))
  let e : R ≃+* Γ(Spec R, ⊤) := (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv
  have hP : P = Q.comap π.appTop.hom :=
    Scheme.comap_germ_maximalIdeal_eq_comap_appTop π q
  have hα : algebraMap R B = π.appTop.hom.comp e.toRingHom :=
    correspondenceRemainingFiniteAlgebra_algebraMap f g h i z w v x
  have hR : Q.comap (algebraMap R B) = P.comap e.toRingHom := by
    rw [hP, Ideal.comap_comap, ← hα]
  let eκ := Ideal.residueFieldRingEquiv (Q.comap (algebraMap R B)) P e hR
  have heκ (a : R) :
      eκ (algebraMap R (Q.comap (algebraMap R B)).ResidueField a) =
        algebraMap Γ(Spec R, ⊤) P.ResidueField (e a) :=
    Ideal.ResidueField.map_algebraMap (Q.comap (algebraMap R B)) P e.toRingHom hR a
  have hdegree :
      Stacks.Length.primeResidueDegree (algebraMap R B)
        (Q.comap (algebraMap R B)) Q =
      Stacks.Length.primeResidueDegree π.appTop.hom P Q := by
    rw [Stacks.Length.primeResidueDegree_of_eq _ _ _ rfl,
      Stacks.Length.primeResidueDegree_of_eq _ _ _ hP]
    letI := (Ideal.ResidueField.map (Q.comap (algebraMap R B)) Q
      (algebraMap R B) rfl).toAlgebra
    letI := (Ideal.ResidueField.map P Q π.appTop.hom hP).toAlgebra
    refine Algebra.finrank_eq_of_equiv_equiv eκ (RingEquiv.refl Q.ResidueField)
      (Ideal.ResidueField.ringHom_ext ?_)
    ext a
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.refl_apply, RingHom.algebraMap_toAlgebra,
      heκ, Ideal.ResidueField.map_algebraMap]
    exact congrArg (algebraMap B Q.ResidueField)
      (congrArg (fun α : R →+* B => α a) hα).symm
  exact hdegree.trans
    (primeResidueDegree_correspondenceRemainingFiniteModel f g h i z w v hz hw x q)

/-- The same degree comparison at the actual image point's ideal, without an
extra hypothesis identifying that ideal with a chosen contracted prime. -/
theorem primeResidueDegree_correspondenceRemainingFiniteAlgebra_at_imagePoint [IsSeparated h]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (q : correspondenceRemainingFiniteModel f g h i z w v x) :
    letI := correspondenceRemainingFiniteAlgebra f g h i z w v x
    Stacks.Length.primeResidueDegree
      (algebraMap (correspondenceRemainingImageStalk f g h i z w v x)
        (correspondenceRemainingFiniteRing f g h i z w v x))
      (correspondenceRemainingFiniteModelStructure f g h i z w v x q).asIdeal
      (Ideal.comap
        ((correspondenceRemainingFiniteModel f g h i z w v x).presheaf.germ ⊤ q trivial).hom
        (IsLocalRing.maximalIdeal
          ((correspondenceRemainingFiniteModel f g h i z w v x).presheaf.stalk q))) =
      (correspondenceLeftIntermediateImageMap f g h i z w v).residueDegree
        (correspondenceRemainingFiniteModelProjection f g h i z w v x q) := by
  letI := correspondenceRemainingFiniteAlgebra f g h i z w v x
  simpa only [correspondenceRemainingFiniteGermPrime_comap_algebraMap f g h i z w v x q] using
    (primeResidueDegree_correspondenceRemainingFiniteAlgebra f g h i z w v hz hw x q)

end Stacks.Chow
