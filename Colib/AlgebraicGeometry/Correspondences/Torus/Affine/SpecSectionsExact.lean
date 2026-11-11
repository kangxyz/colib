/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.ReducedExact
public import Colib.AlgebraicGeometry.Sites.Smooth.Units.Presheaf
public import Colib.AlgebraicGeometry.Sites.Smooth.Units.BoundaryOneComplex

/-!
# The reduced divisor sequence in actual global-section coefficients

The original large boundary-one and ordinary large global-unit presheaves are
retained at `Spec R`. Both endpoint comparisons are induced by the canonical
`ΓSpecIso`, and the middle term remains the actual reduced-torus section.
The resulting sequence is objectwise short exact. This does not construct a
natural transformation on all smooth sources or a sheaf chain map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial

open _root_.AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers

variable {k R : Type u} [Field k] [CommRing R]
variable (f : Spec (.of R) ⟶ Spec (.of k)) [Smooth f] [IsSeparated f] [QuasiCompact f]

/-- The actual global boundary-one coefficient is compared by the original affine counit. -/
def specBoundaryOneIso : (largeBoundaryOnePresheaf k).obj (op (mk f)) ≅
    AddCommGrpCat.of (ULift.{u + 1} (Additive (Polynomial.BoundaryOneRationalFunctions.group R))) :=
  (Polynomial.BoundaryOneRationalFunctions.functor ⋙
    AddCommGrpCat.uliftFunctor.{u + 1, u}).mapIso (Scheme.ΓSpecIso (.of R))

/-- The ordinary global units are compared by the same affine counit, without transfers. -/
def specUnitsIso : (largeUnitsPresheaf (Spec (.of k))).obj (op (mk f)) ≅
    AddCommGrpCat.of (ULift.{u + 1} (Additive Rˣ)) :=
  (ringUnitsFunctor ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}).mapIso
    (Scheme.ΓSpecIso (.of R))

/-- The inverse unit comparison is the actual forward `ΓSpecIso` unit embedding. -/
@[simp] theorem specUnitsIso_inv_apply (v : Rˣ) :
    (specUnitsIso f).inv (ULift.up (Additive.ofMul v)) =
      ULift.up (Additive.ofMul (specGlobalUnit v)) := rfl

variable [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]

/-- The actual boundary-one global coefficient maps by its genuine reduced divisor. -/
def specSectionsReducedBoundaryDivisor : (largeBoundaryOnePresheaf k).obj (op (mk f)) ⟶
    sections (reducedTorus k 1) (Cor.mk (mk f)) :=
  (specBoundaryOneIso f).hom ≫ reducedBoundaryDivisor f

/-- The actual determinant norm takes values in the original ordinary global-unit coefficient. -/
def specSectionsReducedNorm : sections (reducedTorus k 1) (Cor.mk (mk f)) ⟶
    (largeUnitsPresheaf (Spec (.of k))).obj (op (mk f)) :=
  reducedNormApp f ≫ (specUnitsIso f).inv

/-- Its value on a genuine represented cycle is the literal global determinant unit. -/
theorem specSectionsReducedNorm_toReduced
    (z : Cor.mk (mk f) ⟶ Cor.mk (torusPower (Spec (.of k)) 1)) :
    specSectionsReducedNorm f ((toReducedTorus k 1).hom.app (op (Cor.mk (mk f))) (ULift.up z)) =
      ULift.up (Additive.ofMul (specGlobalUnit (powerOneNorm f z).toMul)) := by
  change (specUnitsIso f).inv
    (reducedNormApp f ((toReducedTorus k 1).hom.app (op (Cor.mk (mk f))) (ULift.up z))) = _
  rw [reducedNormApp_toReduced]
  rfl

@[reassoc (attr := simp)] theorem specSectionsReducedBoundaryDivisor_norm :
    specSectionsReducedBoundaryDivisor f ≫ specSectionsReducedNorm f = 0 := by
  simp only [specSectionsReducedBoundaryDivisor, specSectionsReducedNorm, Category.assoc,
    reducedBoundaryDivisor_norm_assoc, zero_comp, comp_zero]

/-- The original global coefficients and canonical quotient, with their concrete maps. -/
def specSectionsReducedDivisorShortComplex : ShortComplex AddCommGrpCat.{u + 1} :=
  ShortComplex.mk (specSectionsReducedBoundaryDivisor f) (specSectionsReducedNorm f)
    (specSectionsReducedBoundaryDivisor_norm f)

/-- Only the actual two affine counits are used in comparing the two concrete sequences. -/
def reducedDivisorSpecSectionsIso : reducedDivisorShortComplex f ≅
    specSectionsReducedDivisorShortComplex f :=
  ShortComplex.isoMk (specBoundaryOneIso f).symm (Iso.refl _) (specUnitsIso f).symm
    (by simp [reducedDivisorShortComplex, specSectionsReducedDivisorShortComplex,
      specSectionsReducedBoundaryDivisor])
    (by simp [reducedDivisorShortComplex, specSectionsReducedDivisorShortComplex,
      specSectionsReducedNorm])

/-- Genuine objectwise exactness with the original boundary-one and ordinary unit coefficients. -/
theorem specSectionsReducedDivisorShortComplex_shortExact :
    (specSectionsReducedDivisorShortComplex f).ShortExact :=
  ShortComplex.shortExact_of_iso (reducedDivisorSpecSectionsIso f)
    (reducedDivisorShortComplex_shortExact f)

end AlgebraicGeometry.NativeTorusPolynomial
