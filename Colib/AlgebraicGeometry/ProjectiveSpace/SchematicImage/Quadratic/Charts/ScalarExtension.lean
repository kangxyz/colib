/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Colib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.Charts.RelativeCoordinates
/-!
# Scalar extension of the unchanged quadratic coordinates

The original monomial functions, coefficient rows and auxiliary row commute with scalar
extension. Both the base-coordinate map and the relative polynomial-coordinate map retain
their actual generators and coefficient maps. No new coordinate tuple is selected.
-/

@[expose] public noncomputable section

open MvPolynomial

universe u

namespace QuadraticIncidence.InfinityChart
variable (E L B C : Type u) [Field E] [Field L] [Algebra E L]
  [CommRing B] [CommRing C] [Algebra E B] [Algebra E C] [Algebra L C]
  [IsScalarTower E L C] (φ : B →ₐ[E] C)
  {σ : Type u} [Fintype σ] (g : σ → B) (d : ℕ)

/-- Each original quadratic function commutes with the actual scalar-extension map. -/
theorem originalFunction_scalarExtension (c : Fin d × Exponent σ → E) (i : Fin d) :
    φ (aeval g (parameterTuple E σ d c i).val) =
      aeval (fun j => φ (g j))
        (parameterTuple L σ d (fun q => algebraMap E L (c q)) i).val := by
  simp only [originalFunction_eq_sum_rows, map_sum, map_mul, AlgHom.commutes,
    monomialFunction, aeval_monomial, Finsupp.prod, map_prod, map_pow, map_one, one_mul,
    ← IsScalarTower.algebraMap_apply E L C]

/-- The whole original quadratic base-coordinate map retains its scalar-extension square. -/
theorem quadraticCoordinateHom_scalarExtension (c : Fin d × Exponent σ → E) :
    φ.toRingHom.comp (quadraticCoordinateHom E B g d c) =
      (quadraticCoordinateHom L C (fun j => φ (g j)) d
        (fun q => algebraMap E L (c q))).comp (MvPolynomial.map (algebraMap E L)) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [quadraticCoordinateHom, ← IsScalarTower.algebraMap_apply E L C]
  · intro i
    simpa [quadraticCoordinateHom] using
      originalFunction_scalarExtension E L B C φ g d c i

end QuadraticIncidence.InfinityChart

namespace QuadraticIncidence.InfinityChart
variable (E L B C : Type u) [Field E] [Field L] [Algebra E L]
  [CommRing B] [CommRing C] [Algebra E B] [Algebra E C] [Algebra L C]
  [IsScalarTower E L C] (φ : B →ₐ[E] C)
  {σ : Type u} [Fintype σ] (g : σ → B) (d : ℕ)

omit [Fintype σ] in
/-- Extending coefficients preserves the original auxiliary row and every tail row. -/
theorem prependParameters_scalarExtension (a : Exponent σ → E)
    (c : Fin d × Exponent σ → E) :
    (fun q => algebraMap E L (prependParameters E d a c q)) =
      prependParameters L d (fun e => algebraMap E L (a e))
        (fun q => algebraMap E L (c q)) := by
  funext q
  rcases q with ⟨i, e⟩
  exact Fin.cases rfl (fun _ => rfl) i

/-- The original relative polynomial-coordinate map commutes with scalar extension. -/
theorem quadraticRelativeCoordinateHom_scalarExtension (a : Exponent σ → E)
    (c : Fin d × Exponent σ → E) :
    φ.toRingHom.comp (quadraticRelativeCoordinateHom E B g d a c) =
      (quadraticRelativeCoordinateHom L C (fun j => φ (g j)) d
        (fun e => algebraMap E L (a e)) (fun q => algebraMap E L (c q))).comp
        (Polynomial.mapRingHom (MvPolynomial.map (algebraMap E L))) := by
  apply Polynomial.ringHom_ext
  · intro p
    have h := DFunLike.congr_fun (quadraticCoordinateHom_scalarExtension E L B C φ g d c) p
    have hE := DFunLike.congr_fun (quadraticRelativeCoordinateHom_comp_C E B g d a c) p
    have hL := DFunLike.congr_fun (quadraticRelativeCoordinateHom_comp_C L C
      (fun j => φ (g j)) d (fun e => algebraMap E L (a e))
      (fun q => algebraMap E L (c q))) (MvPolynomial.map (algebraMap E L) p)
    simp only [RingHom.comp_apply] at hE hL
    simpa only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C, hE, hL] using h
  · simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X,
      quadraticRelativeCoordinateHom, relativeCoordinateHom_X]
    have h := originalFunction_scalarExtension E L B C φ g (d + 1)
      (prependParameters E d a c) 0
    rwa [prependParameters_scalarExtension] at h
end QuadraticIncidence.InfinityChart
