/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.StandardCoordinateChartExactness
public import Colib.AlgebraicGeometry.Scheme.PolynomialLaurentBaseChange

/-! # Bass middle exactness for polynomial and Laurent spectra -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveLine

attribute [local instance] Waldhausen.Additivity.KCommGroup

set_option backward.isDefEq.respectTransparency false in
/-- Over a commutative ring, the image of diagonal polynomial coefficient pullback equals the
kernel of the difference of the two Laurent restrictions in all connective degrees, including
degree zero. Both maps are pullbacks along the actual maps of affine schemes. -/
@[colib_tag "COL-1291", colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/BassZeroMiddleExactness.lean:31-65"
  "adaptation" "Literal affine coefficient and Laurent maps in all connective degrees"]
theorem affineBass_coefficientPair_range_eq_ker (R : CommRingCat.{u}) (n : ℕ) :
    ((perfectKPullback (PolynomialLaurent.polynomialProjection R) n).prod
      (perfectKPullback (PolynomialLaurent.polynomialProjection R) n)).range =
    (GroupMayerVietoris.difference (perfectKPullback (laurentToPolynomial R) n)
      (perfectKPullback (laurentMinus R) n)).ker := by
  let X : QuasiCompactSchemes.{u} := ⟨Spec R, inferInstanceAs (CompactSpace (Spec R))⟩
  let A : Spec (.of (Polynomial R)) ≅ (Relative.polynomialFunctor.obj X).obj :=
    Relative.polynomialSpecIso R
  let B : Spec (.of (LaurentPolynomial R)) ≅ (Relative.laurentFunctor.obj X).obj :=
    Relative.laurentSpecIso R
  let f := perfectKPullback A.hom n
  let g := perfectKPullback B.hom n
  let e := (f.comp (MonoidHom.fst _ _)).prod (f.comp (MonoidHom.snd _ _))
  let P := relativePolynomialPair X n
  let L := relativeLaurentDifference X n
  let p := perfectKPullback (PolynomialLaurent.polynomialProjection R) n
  let l := GroupMayerVietoris.difference (perfectKPullback (laurentToPolynomial R) n)
    (perfectKPullback (laurentMinus R) n)
  have hf : Function.Bijective f := perfectKPullback_iso_bijective A n
  have hg : Function.Injective g := (perfectKPullback_iso_bijective B n).injective
  have he : Function.Bijective e :=
    ⟨fun _ _ h => Prod.ext (hf.injective (congrArg Prod.fst h))
      (hf.injective (congrArg Prod.snd h)),
      fun z => by
        obtain ⟨x, hx⟩ := hf.surjective z.1
        obtain ⟨y, hy⟩ := hf.surjective z.2
        exact ⟨(x, y), Prod.ext hx hy⟩⟩
  have hcoeff (x : _) : e (P x) = (p.prod p) x := by
    have h : f.comp (perfectKPullback (Relative.polynomialProjection.app X).hom n) = p := by
      dsimp only [f]
      rw [← perfectKPullback_comp]
      exact congrArg (fun k => perfectKPullback k n) (Relative.polynomialSpecIso_hom_fst R)
    exact Prod.ext (DFunLike.congr_fun h x) (DFunLike.congr_fun h x)
  have hdiff (z : _) : g (L z) = l (e z) := by
    change g (perfectKPullback (Relative.plus.app X).hom n z.1 *
      (perfectKPullback (Relative.minus.app X).hom n z.2)⁻¹) = _
    have hp : B.hom ≫ (Relative.plus.app X).hom = laurentToPolynomial R ≫ A.hom :=
      (Relative.polynomialLaurentSpecIso_plus R).symm
    have hm : B.hom ≫ (Relative.minus.app X).hom = laurentMinus R ≫ A.hom :=
      (Relative.polynomialLaurentSpecIso_minus R).symm
    rw [map_mul, map_inv]
    apply congrArg₂ (fun a b => a * b⁻¹)
    · exact DFunLike.congr_fun
        ((perfectKPullback_comp B.hom (Relative.plus.app X).hom n).symm.trans
          ((congrArg (fun k => perfectKPullback k n) hp).trans
            (perfectKPullback_comp (laurentToPolynomial R) A.hom n))) z.1
    · exact DFunLike.congr_fun
        ((perfectKPullback_comp B.hom (Relative.minus.app X).hom n).symm.trans
          ((congrArg (fun k => perfectKPullback k n) hm).trans
            (perfectKPullback_comp (laurentMinus R) A.hom n))) z.2
  have hrel : P.range = L.ker := relativePolynomialPair_range_eq_ker X n
  ext z
  obtain ⟨y, rfl⟩ := he.surjective z
  constructor
  · rintro ⟨x, hx⟩
    have hxy : P x = y := he.injective ((hcoeff x).trans hx)
    have hy : y ∈ L.ker := hrel ▸ ⟨x, hxy⟩
    change l (e y) = 1
    rw [← hdiff, show L y = 1 from hy, map_one]
  · intro hy
    have hz : y ∈ L.ker := by
      change L y = 1
      apply hg
      rw [hdiff, map_one]
      exact hy
    obtain ⟨x, hx⟩ := hrel.symm ▸ hz
    exact ⟨x, (hcoeff x).symm.trans (congrArg e hx)⟩

end AlgebraicGeometry.Scheme.ProjectiveLine
