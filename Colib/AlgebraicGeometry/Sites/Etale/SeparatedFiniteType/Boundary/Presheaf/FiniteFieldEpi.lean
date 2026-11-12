/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Presheaf.FinitePolynomialImage
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Contraction.Inputs
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Presheaf.PolynomialZeroChart

/-! # The canonical original-presheaf contraction boundary is epimorphic

Over a finite field, the actual two-prime corrections give original image
sieves on open neighborhoods of every closed point of each original zero fiber.
These opens form a genuine Jacobson open cover before passage to the Nisnevich
sieve. The coefficient presheaf is never replaced by its sheafification.
-/

/-!
Adapted from `Motivic/Cohomology/A1/Boundary/Presheaf/FiniteFieldEpi.lean`
at `a6805c4a87cdfd7717dd7a94039246a167f15380`,
blob `cad573d6b4486917b7111a452ae9fc0b156d1b2e`. The coefficient maps, full zero schemes and
original puncture projections are retained.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary.OriginalPresheaf
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {k : Type u} [Field k] [Finite k]

/-- The actual canonical boundary morphism for every homotopy-invariant original
presheaf with transfers is epimorphic over a finite field. -/
theorem contractionToBoundary_epi_of_finite (X : SmoothSite (Spec (.of k)))
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    Epi (contractionToBoundary X P) := by
  let : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace
    (Y := Spec (.of k)) (show X.left ⟶ Spec (.of k) from X.hom)
  apply presheafBoundary_epi_of_closedPoint_generators
    ((PresheafWithTransfers.toPresheaf k).obj P)
    (SmoothSite.Contraction.openInclusion.app X) (SmoothSite.Contraction.nativeAffineSection
      (.of k) X 0)
    (contractionToBoundary X P)
  intro W d w hw
  obtain ⟨C⟩ := exists_polynomialZeroBoundaryChart_of_closed (k := k) X W w hw
  let : CommRing C.R := C.ring
  let : IsDomain C.R := C.domain
  let : Algebra k C.R := C.algebra
  let : Algebra.Smooth k C.R := C.smooth
  let : IsAffine C.Y.left := C.affine
  let : Etale C.p.left := C.etale
  let : (PrimeSpectrum.comap (Polynomial.evalRingHom (0 : C.R)) C.wR).asIdeal.IsMaximal :=
    C.markedMaximal
  let : IsOpenImmersion C.vR.left := C.open_vR
  let ℓ := ringChar k
  let : Fact ℓ.Prime := ⟨CharP.prime_ringChar k⟩
  obtain ⟨V, v, hv, hw', hi⟩ := exists_finite_polynomial_boundary_image_neighborhood (k := k)
    X P hP W C.R ℓ C.p C.wR C.sR C.section_eq C.zero_cartesian C.vR C.eR
      C.ambient_eq C.mark_eq d
  exact ⟨V, v, hv, C.point_eq ▸ hw', hi⟩

/-- The actual finite-field producer supplies the original canonical Epi family. -/
theorem canonicalBoundaryEpi_of_finite : CanonicalBoundaryEpi k := by
  intro X P hP
  exact contractionToBoundary_epi_of_finite X P hP

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary.OriginalPresheaf
