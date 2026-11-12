/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.QuadraticPairs
public import Colib.AlgebraicGeometry.Sites.Smooth.Affine.LineCoordinates

/-!
# The quadratic family on the native affine-line cylinder

The polynomial parameter is compared to the original native affine-line
cylinder. The endpoints are the original affine sections at zero and one,
and their graphs recover the same split cycles.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
open AlgebraicGeometry.Scheme SmoothSite SmoothSite.Contraction
open AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.PolynomialOpenQuotient
open AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial

variable {k R : Type u} [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Gₖ" => multiplicativeGroupObject Sₖ
local notation "U" => affineSite k R
local notation "V" => lineSite (k := k) (R := R)
local notation "e" => lineCylinderIso (k := k) (R := R)
local notation "γ" => CategoryTheory.Functor.map (Cor.graphFunctor k)
local notation "ev(" r ")" => Spec.map (CommRingCat.ofHom (evalRingHom (r : R)))
set_option quotPrecheck false in
local notation "unitPoint(" f "," a ")" =>
  SmoothSite.homMk (X := SmoothSite.mk f) (Y := Gₖ)
    (nativeAffineTorusPoint f a).left (affineUnitPoint_over f a)

private theorem lineEvaluation_projection (r : R) :
    ev(r) ≫ polynomialProjection (.of R) = 𝟙 _ := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (Polynomial.C : R →+* R[X]) ≫
      CommRingCat.ofHom (evalRingHom r) = 𝟙 _ := by
    ext a
    exact eval_C
  rw [h, Spec.map_id]

private theorem lineEvaluation_base (r : R) : ev(r) ≫ (V).hom = (U).hom := by
  change ev(r) ≫ (polynomialProjection (.of R) ≫ (U).hom) = _
  rw [← Category.assoc, lineEvaluation_projection, Category.id_comp]

private def lineSection (r : R) : U ⟶ V :=
  homMk (ev(r)) (lineEvaluation_base r)

private theorem lineSection_polynomialProduct (r : k) :
    lineSection (k := k) (algebraMap k R r) ≫ linePolynomialProductIso.hom =
      polynomialAffineSection (.of k) U r := by
  apply product_hom_ext
  · simp only [Category.assoc, linePolynomialProductIso_projection,
      polynomialAffineSection, productLift_fst]
    apply MorphismProperty.Over.Hom.ext
    exact lineEvaluation_projection _
  · simp only [Category.assoc, polynomialAffineSection, productLift_snd]
    apply MorphismProperty.Over.Hom.ext
    change ev(algebraMap k R r) ≫ (ambientIso (algebraMap k R)).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap k R)) ≫
        Spec.map (CommRingCat.ofHom (evalRingHom r))
    rw [ambientIso_snd, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro a
      simp
    · simp

private theorem lineSection_cylinder (r : k) :
    lineSection (k := k) (algebraMap k R r) ≫ (e).hom = nativeAffineSection (.of k) U r := by
  apply (cancel_mono (affineCylinderPolynomialIso (.of k) U).hom).mp
  simp only [lineCylinderIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, nativeAffineSection_polynomialIso]
  exact lineSection_polynomialProduct r

variable [IsNoetherianRing R] [IsDomain R]

/-- The actual finite flat quadratic pencil on the native cylinder over the affine source. -/
def unitProductCylinderCycle (a b : Rˣ) :
    Cor.mk (affineLineCylinder.obj U) ⟶ Cor.mk Gₖ :=
  γ (e).inv ≫ (unitProductPencilCycle (V).hom a b : Cor.mk V ⟶ Cor.mk Gₖ)

set_option maxHeartbeats 500000 in
-- The graph comparison checks both presentations of the original smooth object.
private theorem graph_lineSection_comp_unitProductPencilCycle
    (r : R) [Smooth (ev(r) ≫ (V).hom)] [IsSeparated (ev(r) ≫ (V).hom)]
    [QuasiCompact (ev(r) ≫ (V).hom)] (a b u v : Rˣ)
    (h : γ (coefficientGraph (V).hom (evalRingHom r)) ≫
        (unitProductPencilCycle (V).hom a b : Cor.mk V ⟶ Cor.mk Gₖ) =
      γ (unitPoint(ev(r) ≫ (V).hom,u)) + γ (unitPoint(ev(r) ≫ (V).hom,v))) :
    γ (lineSection (k := k) r) ≫
        (unitProductPencilCycle (V).hom a b : Cor.mk V ⟶ Cor.mk Gₖ) =
      γ (unitPoint((U).hom, u)) + γ (unitPoint((U).hom, v)) := by
  let i : U ⟶ mk (ev(r) ≫ (V).hom) := homMk (𝟙 _) (by
    change 𝟙 _ ≫ (ev(r) ≫ (V).hom) = (U).hom
    exact (Category.id_comp _).trans (lineEvaluation_base r))
  have hi : i ≫ coefficientGraph (V).hom (evalRingHom r) = lineSection (k := k) r := by
    apply MorphismProperty.Over.Hom.ext
    exact Category.id_comp _
  have hiUnit (z : Rˣ) :
      i ≫ unitPoint(ev(r) ≫ (V).hom, z) = unitPoint((U).hom, z) := by
    apply MorphismProperty.Over.Hom.ext
    let pointMap (g : Spec (.of R) ⟶ Sₖ) :
        Spec (.of R) ⟶ multiplicativeGroupBaseChange Sₖ := (nativeAffineTorusPoint g z).left
    change 𝟙 _ ≫ pointMap (ev(r) ≫ (V).hom) = pointMap (U).hom
    exact (Category.id_comp _).trans (congrArg pointMap (lineEvaluation_base r))
  rw [← hi, Functor.map_comp, Category.assoc, h, Preadditive.comp_add, ← Functor.map_comp,
    ← Functor.map_comp, hiUnit, hiUnit]

variable [IsIntegrallyClosed R]

/-- The zero endpoint is the product graph plus the unit graph on the same source. -/
theorem graph_zero_comp_unitProductCylinderCycle (a b : Rˣ) :
    γ (nativeAffineSection (.of k) U 0) ≫ unitProductCylinderCycle (k := k) a b =
      γ (unitPoint((U).hom, a * b)) + γ (unitPoint((U).hom, 1)) := by
  have h : lineSection (k := k) (0 : R) ≫ (e).hom = nativeAffineSection (.of k) U 0 := by
    simpa only [map_zero] using lineSection_cylinder (R := R) (0 : k)
  rw [unitProductCylinderCycle, ← Functor.map_comp_assoc, ← h, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]
  have hbase := lineEvaluation_base (k := k) (R := R) 0
  let : Smooth (ev(0) ≫ (V).hom) := hbase.symm ▸ inferInstanceAs (Smooth (U).hom)
  let : IsSeparated (ev(0) ≫ (V).hom) := hbase.symm ▸ inferInstanceAs (IsSeparated (U).hom)
  let : QuasiCompact (ev(0) ≫ (V).hom) := hbase.symm ▸ inferInstanceAs (QuasiCompact (U).hom)
  exact graph_lineSection_comp_unitProductPencilCycle (0 : R) a b (a * b) 1
    (graph_zero_comp_unitProductPencilCycle (V).hom a b)

/-- The one endpoint is the two original unit graphs on the same source. -/
theorem graph_one_comp_unitProductCylinderCycle (a b : Rˣ) :
    γ (nativeAffineSection (.of k) U 1) ≫ unitProductCylinderCycle (k := k) a b =
      γ (unitPoint((U).hom, a)) + γ (unitPoint((U).hom, b)) := by
  have h : lineSection (k := k) (1 : R) ≫ (e).hom = nativeAffineSection (.of k) U 1 := by
    simpa only [map_one] using lineSection_cylinder (R := R) (1 : k)
  rw [unitProductCylinderCycle, ← Functor.map_comp_assoc, ← h, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]
  have hbase := lineEvaluation_base (k := k) (R := R) 1
  let : Smooth (ev(1) ≫ (V).hom) := hbase.symm ▸ inferInstanceAs (Smooth (U).hom)
  let : IsSeparated (ev(1) ≫ (V).hom) := hbase.symm ▸ inferInstanceAs (IsSeparated (U).hom)
  let : QuasiCompact (ev(1) ≫ (V).hom) := hbase.symm ▸ inferInstanceAs (QuasiCompact (U).hom)
  exact graph_lineSection_comp_unitProductPencilCycle (1 : R) a b a b
    (graph_one_comp_unitProductPencilCycle (V).hom a b)

end AlgebraicGeometry.NativeTorusPolynomial
