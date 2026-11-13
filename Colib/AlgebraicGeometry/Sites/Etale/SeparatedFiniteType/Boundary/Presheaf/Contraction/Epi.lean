/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Presheaf.PolynomialImage
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Presheaf.PolynomialZeroChart
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.PolynomialZeroOriginalEtalePresentation

/-! # The canonical original-presheaf contraction boundary is epimorphic

Over an infinite field, the two original section corrections give actual image
sieves on open neighborhoods of every closed point of each original zero fiber.
These opens form a genuine Jacobson open cover before passage to the Nisnevich
sieve. The coefficient presheaf is never replaced by its sheafification.
-/

/-! Adapted from `Motivic/Cohomology/A1/Boundary/Presheaf/Contraction/Epi.lean` at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`.
The active native group objects, full closed markings, original coefficient
universe and original beta-minus-alpha identity are retained. -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary.OriginalPresheaf
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {k : Type u} [Field k] [Infinite k]

/-- The actual canonical boundary morphism for every homotopy-invariant original
presheaf with transfers is epimorphic over an infinite field. -/
theorem contractionToBoundary_epi (X : SmoothSite (Spec (.of k)))
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    Epi (contractionToBoundary X P) := by
  let : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace
    (Y := Spec (.of k)) (show X.left ⟶ Spec (.of k) from X.hom)
  apply presheafBoundary_epi_of_closedPoint_generators
    ((PresheafWithTransfers.toPresheaf k).obj P)
    (SmoothSite.Contraction.openInclusion.app X)
    (SmoothSite.Contraction.nativeAffineSection (.of k) X 0)
    (contractionToBoundary X P)
  intro W d w hw
  obtain ⟨C⟩ := exists_polynomialZeroBoundaryChart_of_closed (k := k) X W w hw
  let : CommRing C.R := C.ring
  let : IsDomain C.R := C.domain
  let : Algebra k C.R := C.algebra
  let : Algebra.Smooth k C.R := C.smooth
  let : IsAffine C.Y.left := C.affine
  let : Etale C.p.left := C.etale
  let : QuasiCompact C.p.left := SmoothSite.quasiCompact_hom C.p
  let : IsSeparated C.p.left := SmoothSite.isSeparated_hom C.p
  let : IsOpenImmersion C.vR.left := C.open_vR
  let xR := PrimeSpectrum.comap (Polynomial.evalRingHom (0 : C.R)) C.wR
  let : xR.asIdeal.IsMaximal := C.markedMaximal
  obtain ⟨presentation⟩ :=
    QuadraticIncidence.InfinityChart.nonempty_polynomialZero_originalEtalePresentation
      k C.R xR C.p.left C.sR C.section_eq C.zero_cartesian
  obtain ⟨V, v, hv, hw', hi⟩ := exists_polynomial_boundary_image_neighborhood (k := k)
    X P hP W C.R C.p (PolynomialOpenQuotient.inclusion (Polynomial.X : Polynomial C.R))
    (PolynomialOpenQuotient.source (Polynomial.X : Polynomial C.R) ≫ C.sR)
    C.wR presentation C.sR C.section_eq C.vR C.eR C.ambient_eq C.mark_eq d
  exact ⟨V, v, hv, C.point_eq ▸ hw', hi⟩

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary.OriginalPresheaf
