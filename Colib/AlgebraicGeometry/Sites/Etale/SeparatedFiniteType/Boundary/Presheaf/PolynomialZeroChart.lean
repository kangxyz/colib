/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Contraction.IntegralWholeZeroRefinement
public import Colib.AlgebraicGeometry.Sites.Smooth.Affine.WholeZeroCoordinates
public import Colib.AlgebraicGeometry.Sites.Smooth.Affine.ZeroPoint

/-!
# Polynomial coordinates on a whole-zero boundary chart

At a closed point of the original zero-section pullback, transport the actual
integral affine neighborhood to polynomial coordinates. The original étale
map, full Cartesian zero fiber and point retain their original projections.

Adapted from `Motivic/Cohomology/A1/Boundary/Presheaf/FiniteFieldEpi.lean`
at `a6805c4a87cdfd7717dd7a94039246a167f15380`,
blob `cad573d6b4486917b7111a452ae9fc0b156d1b2e`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
open _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineSectionCoordinates

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary.OriginalPresheaf

open _root_.AlgebraicGeometry.PolynomialOpenQuotient
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {k : Type u} [Field k]

/-- Polynomial coordinates and the literal original projections of a marked boundary chart. -/
structure PolynomialZeroBoundaryChart (X : SmoothSite (Spec (.of k)))
    (W : EtaleSeparatedFiniteType (SmoothSite.Contraction.affineLineCylinder.obj X).left)
    (w : ((baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left).obj W).left)
    where
  /-- The coordinate ring of the integral affine zero neighborhood. -/
  R : Type u
  /-- The commutative ring structure used in the zero chart and its polynomial line. -/
  [ring : CommRing R]
  [domain : IsDomain R]
  /-- The `k`-algebra structure on the coordinate ring of the zero chart. -/
  [algebra : Algebra k R]
  [smooth : Algebra.Smooth k R]
  /-- The affine étale neighborhood of the polynomial line carrying the marked lift. -/
  Y : SmoothSite (Spec (.of k))
  [affine : IsAffine Y.left]
  /-- The étale map from `Y` to the polynomial line over `R`. -/
  p : Y ⟶ SmoothSite.lineSite (k := k) (R := R)
  [etale : Etale p.left]
  /-- The point of `Spec R` sent to the original marked point `w` by `vR`. -/
  wR : Spec (.of R)
  [markedMaximal : (PrimeSpectrum.comap (Polynomial.evalRingHom (0 : R)) wR).asIdeal.IsMaximal]
  /-- The lift of the polynomial zero section identifying its full fiber in `Y`. -/
  sR : Spec (.of R) ⟶ Y.left
  section_eq : sR ≫ p.left = Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))
  zero_cartesian : IsPullback sR (𝟙 _) p.left
    (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))))
  /-- The open chart map from `Spec R` into the zero-section pullback of `W`. -/
  vR : SmoothSite.affineSite k R ⟶
    (toSmoothSite X).obj ((baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X
      0).left).obj W)
  [open_vR : IsOpenImmersion vR.left]
  /-- The map from the polynomial étale chart to the original neighborhood `W` over the cylinder. -/
  eR : Y ⟶ (toSmoothSite (SmoothSite.Contraction.affineLineCylinder.obj X)).obj W
  ambient_eq : p ≫ (lineCylinderIso (k := k) (R := R)).hom ≫
    SmoothSite.Contraction.affineLineCylinder.map
      (vR ≫ toBase X ((baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X
        0).left).obj W)) = eR ≫ toBase (SmoothSite.Contraction.affineLineCylinder.obj X) W
  mark_eq : sR ≫ eR.left = vR.left ≫
    pullback.fst W.hom (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left
  point_eq : vR.left wR = w

attribute [local instance] sectionsAlgebra

/-- Every closed point of the original zero pullback has an actual polynomial boundary chart. -/
theorem exists_polynomialZeroBoundaryChart_of_closed (X : SmoothSite (Spec (.of k)))
    (W : EtaleSeparatedFiniteType (SmoothSite.Contraction.affineLineCylinder.obj X).left)
    (w : ((baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left).obj W).left)
    (hw : IsClosed ({w} : Set ((baseChange
      (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left).obj W).left)) :
    Nonempty (PolynomialZeroBoundaryChart X W w) := by
  obtain ⟨V₀, v₀, hV, hI, hv, hwV, E₀, e₀, q₀, a₀, z₀,
    hE, hq, hqc, hqs, H₀, haz, _hzq, hze⟩ :=
    exists_integral_whole_zero_neighborhood_refinement X W w
  let : IsAffine V₀.left := hV
  let : IsIntegral V₀.left := hI
  let : IsOpenImmersion v₀.left := hv
  let : IsAffine E₀.left := hE
  let : Etale q₀.left := hq
  let : QuasiCompact q₀.left := hqc
  let : IsSeparated q₀.left := hqs
  obtain ⟨t₀, ht₀⟩ := hwV
  have htClosed : IsClosed ({t₀} : Set V₀.left) := by
    have heq : v₀.left ⁻¹' ({w} : Set _) = {t₀} := by
      ext t
      change v₀.left t = w ↔ t = t₀
      rw [← ht₀]
      exact v₀.left.isOpenEmbedding.injective.eq_iff
    rw [← heq]
    exact hw.preimage v₀.left.continuous
  let B₀ := (toSmoothSite X).obj V₀
  let : IsAffine B₀.left := hV
  let : IsIntegral B₀.left := hI
  let R := Γ(B₀.left, ⊤)
  let : Algebra k R := sectionsAlgebra B₀
  let : Algebra.Smooth k R := sectionsSmooth B₀
  let : IsDomain R := inferInstanceAs (IsDomain Γ(B₀.left, ⊤))
  let Y := (toSmoothSite (SmoothSite.Contraction.affineLineCylinder.obj X)).obj E₀
  let : IsAffine Y.left := hE
  let wR : Spec (.of R) := (affineIso B₀).inv.left t₀
  let xR : PrimeSpectrum (Polynomial R) :=
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) wR
  let : xR.asIdeal.IsMaximal := affineZeroPoint_isMaximal B₀ t₀ htClosed
  let qS := (toSmoothSite (SmoothSite.Contraction.affineLineCylinder.obj X)).map q₀ ≫
    (parameterProductUnderlyingIso X (SmoothSite.additiveGroupObject (Spec (.of k)))).hom.app V₀
  let p : Y ⟶ SmoothSite.lineSite (k := k) (R := R) :=
    qS ≫ (affineLineIso B₀).inv
  have hpLeft : p.left = q₀.left ≫ (affineLineIso B₀).inv.left := by
    change (q₀.left ≫ 𝟙 _) ≫ (affineLineIso B₀).inv.left = _
    rw [Category.comp_id]
  let : IsIso (affineLineIso B₀).inv.left :=
    inferInstanceAs (IsIso ((SmoothSite.forgetScheme (Spec (.of k))).mapIso
      (affineLineIso B₀)).inv)
  let : Etale p.left := by
    rw [hpLeft]
    infer_instance
  let sR := (affineIso B₀).hom.left ≫ a₀
  have HR : IsPullback sR (𝟙 _) p.left
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) := by
    rw [hpLeft]
    exact affineLineIso_wholeZero_isPullback B₀ q₀.left a₀ H₀
  have hsR : sR ≫ p.left = Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) :=
    HR.w.trans (Category.id_comp _)
  let vR := (affineIso B₀).hom ≫ (toSmoothSite X).map v₀
  let eR := (toSmoothSite (SmoothSite.Contraction.affineLineCylinder.obj X)).map e₀
  let : IsIso (affineIso B₀).hom.left :=
    inferInstanceAs (IsIso ((SmoothSite.forgetScheme (Spec (.of k))).mapIso (affineIso B₀)).hom)
  let : IsOpenImmersion vR.left := by
    change IsOpenImmersion ((affineIso B₀).hom.left ≫ v₀.left)
    infer_instance
  have hbase : vR ≫ toBase X ((baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X
    0).left).obj W) =
      (affineIso B₀).hom ≫ toBase X V₀ := by
    change ((affineIso B₀).hom ≫ (toSmoothSite X).map v₀) ≫ _ = _
    rw [Category.assoc]
    congr 1
    exact MorphismProperty.Over.Hom.ext (MorphismProperty.Over.w v₀)
  have hp : p ≫ (lineCylinderIso (k := k) (R := R)).hom ≫
      SmoothSite.Contraction.affineLineCylinder.map
        (vR ≫ toBase X ((baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X
          0).left).obj W)) =
      eR ≫ toBase (SmoothSite.Contraction.affineLineCylinder.obj X) W := by
    have hpc : p ≫ (affineLineIso B₀).hom = qS := by
      simp only [p, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    calc
      _ = (p ≫ (affineLineIso B₀).hom) ≫ SmoothSite.Contraction.affineLineCylinder.map (toBase X
        V₀) := by
        simp only [hbase, Functor.map_comp, Functor.mapIso_hom, affineLineIso, Iso.trans_hom,
          cylinderIso, Category.assoc]
      _ = qS ≫ SmoothSite.Contraction.affineLineCylinder.map (toBase X V₀) := by rw [hpc]
      _ = _ := by
        apply MorphismProperty.Over.Hom.ext
        change (q₀.left ≫ 𝟙 _) ≫ ((cylinderNeighborhood X).obj V₀).hom = e₀.left ≫ W.hom
        rw [Category.comp_id, MorphismProperty.Over.w q₀, MorphismProperty.Over.w e₀]
  have haOriginal : a₀ ≫ e₀.left = v₀.left ≫
      pullback.fst W.hom (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left := by
    have hm : ((baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left).map
      e₀).left ≫
        pullback.fst W.hom (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left =
      pullback.fst E₀.hom (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left ≫ e₀.left :=
      pullback.lift_fst _ _ _
    calc
      _ = z₀.left ≫ pullback.fst E₀.hom
          (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left ≫ e₀.left := by
        rw [← haz, Category.assoc]
      _ = z₀.left ≫ ((baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X
        0).left).map e₀).left ≫
          pullback.fst W.hom (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left := by
            rw [hm]
      _ = _ := congrArg (fun f => f.left ≫
        pullback.fst W.hom (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left) hze
  have hmark : sR ≫ eR.left = vR.left ≫
      pullback.fst W.hom (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left := by
    change ((affineIso B₀).hom.left ≫ a₀) ≫ e₀.left =
      ((affineIso B₀).hom.left ≫ v₀.left) ≫ _
    rw [Category.assoc, haOriginal, Category.assoc]
  have hwR : vR.left wR = w := by
    change v₀.left (V₀.left.isoSpec.inv (V₀.left.isoSpec.hom t₀)) = w
    have ht := congrArg (fun f : V₀.left ⟶ V₀.left => f t₀) V₀.left.isoSpec.hom_inv_id
    change V₀.left.isoSpec.inv (V₀.left.isoSpec.hom t₀) = t₀ at ht
    rw [ht, ht₀]
  let : (PrimeSpectrum.comap (Polynomial.evalRingHom (0 : R)) wR).asIdeal.IsMaximal :=
    inferInstanceAs xR.asIdeal.IsMaximal
  exact ⟨{
    R := R
    ring := inferInstance
    domain := inferInstance
    algebra := inferInstance
    smooth := inferInstance
    Y := Y
    affine := hE
    p := p
    etale := inferInstance
    wR := wR
    markedMaximal := inferInstance
    sR := sR
    section_eq := hsR
    zero_cartesian := HR
    vR := vR
    open_vR := inferInstance
    eR := eR
    ambient_eq := hp
    mark_eq := hmark
    point_eq := hwR }⟩

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary.OriginalPresheaf
