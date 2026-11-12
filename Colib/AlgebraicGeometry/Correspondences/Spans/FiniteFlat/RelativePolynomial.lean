/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.FiniteFlatProduct
public import Colib.AlgebraicGeometry.Chow.PolynomialCurveCycles
public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.Graph
public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.Isomorphism
public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.QuotientStalkMultiplicity
public import Colib.AlgebraicGeometry.Scheme.ForgetBaseProduct
public import Colib.AlgebraicGeometry.Scheme.PolynomialQuotient.Ambient
public import Colib.AlgebraicGeometry.Scheme.PolynomialQuotient.MovingOpen

/-!
# Finite-flat polynomial spans over a relative affine line

The source and target of each whole quotient are their native scheme maps.
Multiplying two polynomials adds their quotient cycles with multiplicities,
as seen from the actual stalk kernels.

Adapted from `Motivic/AlgebraicGeometry/Correspondences/Moving/Polynomial/Relative/`
at `motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
files `OpenSpans.lean`, `SpanIdentities.lean`, `LinearGraph.lean` and
`OpenRestriction.lean`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial Stacks.Chow
open AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace AlgebraicGeometry.PolynomialOpenQuotient

open _root_.AlgebraicGeometry.Scheme

variable {R A : Type u} [CommRing R] [CommRing A] (σ : R →+* A)

/-- The polynomial product with its literal source and target, viewed over
the original smaller base. -/
def relativePolynomialAmbient {S : Scheme.{u}} (b : Spec (.of R) ⟶ S) :
    Spec (.of A[X]) ⟶
      pullback (Spec.map (CommRingCat.ofHom σ) ≫ b) (polynomialProjection (.of R) ≫ b) :=
  (ambientIso σ).hom ≫
    forgetBaseProductMap b (Spec.map (CommRingCat.ofHom σ)) (polynomialProjection (.of R))

instance {S : Scheme.{u}} (b : Spec (.of R) ⟶ S) [IsSeparated b] :
    IsClosedImmersion (relativePolynomialAmbient σ b) := by
  unfold relativePolynomialAmbient
  infer_instance

@[reassoc (attr := simp)]
theorem relativePolynomialAmbient_fst {S : Scheme.{u}} (b : Spec (.of R) ⟶ S) :
    relativePolynomialAmbient σ b ≫ pullback.fst _ _ = polynomialProjection (.of A) := by
  rw [relativePolynomialAmbient, Category.assoc, forgetBaseProductMap_fst]
  exact ambientIso_fst σ

@[reassoc (attr := simp)]
theorem relativePolynomialAmbient_snd {S : Scheme.{u}} (b : Spec (.of R) ⟶ S) :
    relativePolynomialAmbient σ b ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom σ)) := by
  rw [relativePolynomialAmbient, Category.assoc, forgetBaseProductMap_snd]
  exact ambientIso_snd σ

private theorem inclusion_ker_stalk (p : A[X]) (x : Spec (.of A[X])) :
    IdealSheafData.stalk (inclusion p).ker x =
      Ideal.span {NativeTorusPolynomial.polynomialGerm x p} := by
  have htop : (inclusion p).ker.ideal ⟨⊤, isAffineOpen_top _⟩ =
      (Ideal.span {p}).map (Scheme.ΓSpecIso (.of A[X])).inv.hom := by
    rw [Scheme.Hom.ker_apply]
    change RingHom.ker (Spec.map (CommRingCat.ofHom (AdjoinRoot.mk p))).appTop.hom = _
    rw [← RingHom.ker_equiv_comp _ (Scheme.ΓSpecIso (.of (AdjoinRoot p))).commRingCatIsoToRingEquiv]
    change RingHom.ker ((Scheme.ΓSpecIso (.of (AdjoinRoot p))).hom.hom.comp
      (inclusion p).appTop.hom) = _
    rw [← CommRingCat.hom_comp]
    unfold inclusion
    rw [Scheme.ΓSpecIso_naturality, CommRingCat.hom_comp, ← RingHom.comap_ker]
    change Ideal.comap (Scheme.ΓSpecIso (.of A[X])).hom.hom (RingHom.ker (AdjoinRoot.mk p)) = _
    rw [show RingHom.ker (AdjoinRoot.mk p) = Ideal.span {p} from Ideal.mk_ker]
    exact (Ideal.map_symm (Scheme.ΓSpecIso (.of A[X])).commRingCatIsoToRingEquiv).symm
  rw [IdealSheafData.stalk_eq_map_germ _ x ⟨⊤, isAffineOpen_top _⟩ trivial,
    htop, Ideal.map_map, Ideal.map_span, Set.image_singleton]
  rfl

/-- The quotient of a monic product has the sum of the two full quotient cycles. -/
theorem quotientFundamentalCycle_mul [IsNoetherianRing A]
    (p q : A[X]) (hp : p.Monic) (hq : q.Monic) :
    finiteCyclePushforward (inclusion (p * q)) (AlgebraicCycle.fundamentalCycle _) =
      finiteCyclePushforward (inclusion p) (AlgebraicCycle.fundamentalCycle _) +
        finiteCyclePushforward (inclusion q) (AlgebraicCycle.fundamentalCycle _) := by
  let π := polynomialProjection (.of A)
  have hfin (d : A[X]) (hd : d.Monic) : IsFinite (inclusion d ≫ π) := by
    rw [inclusion_projection]
    exact source_finite d hd
  have hflat (d : A[X]) (hd : d.Monic) : Flat (inclusion d ≫ π) := by
    rw [inclusion_projection]
    exact source_flat d hd
  let := hfin p hp
  let := hfin q hq
  let := hfin (p * q) (hp.mul hq)
  let := hflat p hp
  let := hflat q hq
  let := hflat (p * q) (hp.mul hq)
  apply finiteCyclePushforward_fundamentalCycle_mul_of_stalk_ker π
  intro x _
  refine ⟨NativeTorusPolynomial.polynomialGerm x p, NativeTorusPolynomial.polynomialGerm x q,
    inclusion_ker_stalk p x, inclusion_ker_stalk q x, ?_,
    NativeTorusPolynomial.polynomialGerm_mem_nonZeroDivisors x q hq⟩
  rw [inclusion_ker_stalk, map_mul]

namespace SmoothSite

variable {k : Type u} [Field k] [Algebra k R] [Algebra.Smooth k R]
    [Algebra R A] [Algebra k A] [IsScalarTower k R A] [Algebra.Smooth k A]

local notation "U" => sourceSite (k := k) (A := A)
local notation "W" => lineSite (k := k) (R := R)

/-- The whole polynomial span into its original principal open. -/
def openPolynomialSpan (p : A[X]) (hp : p.Monic) (f : R[X])
    (hf : IsUnit (AdjoinRoot.mk p (f.map (algebraMap R A)))) :
    Cor.mk U ⟶ Cor.mk (openSite (k := k) f) := by
  let := source_finite p hp
  let := source_flat p hp
  exact Cor.ofFiniteFlatSpan (source p) (openTarget (algebraMap R A) p f hf) (span_base p f hf)

/-- The same whole polynomial span before restricting the target. -/
def affinePolynomialSpan (p : A[X]) (hp : p.Monic) : Cor.mk U ⟶ Cor.mk W := by
  let := source_finite p hp
  let := source_flat p hp
  exact Cor.ofFiniteFlatSpan (source p) (target (algebraMap R A) p) (affine_base p)

/-- Postcomposition sends the original open lift to the original affine span. -/
theorem openPolynomialSpan_comp_inclusion (p : A[X]) (hp : p.Monic) (f : R[X])
    (hf : IsUnit (AdjoinRoot.mk p (f.map (algebraMap R A)))) :
    openPolynomialSpan (k := k) p hp f hf ≫ (Cor.graphFunctor k).map (openInclusion f) =
      affinePolynomialSpan (k := k) (R := R) p hp := by
  let := source_finite p hp
  let := source_flat p hp
  rw [openPolynomialSpan, Cor.ofFiniteFlatSpan_comp_graph]
  congr 1
  exact openTarget_inclusion _ _ _ _

local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap k R))

/-- The actual whole affine span is the closed quotient followed by the
native product map over the ground field. -/
def affineSpanAmbient :
    Spec (.of A[X]) ⟶ pullback (U).hom (W).hom :=
  relativePolynomialAmbient (algebraMap R A) b ≫
    (pullback.congrHom (coefficient_base (k := k) (R := R) (A := A)) rfl).hom

instance : IsClosedImmersion (affineSpanAmbient (k := k) (R := R) (A := A)) := by
  let : IsAffineHom b := isAffineHom_of_isAffine b
  unfold affineSpanAmbient
  infer_instance

theorem affineSpanAmbient_quotient (p : A[X]) :
    pullback.lift (source p) (target (algebraMap R A) p) (affine_base (k := k) p) =
      inclusion p ≫ affineSpanAmbient (k := k) (R := R) := by
  apply pullback.hom_ext <;>
    simp [affineSpanAmbient, target, pullback.congrHom_hom, Category.assoc]

instance (p : A[X]) : IsClosedImmersion
    (pullback.lift (source p) (target (algebraMap R A) p) (affine_base (k := k) p)) := by
  rw [affineSpanAmbient_quotient]
  infer_instance

private theorem affinePolynomialSpan_val [IsNoetherianRing A] (p : A[X]) (hp : p.Monic) :
    (affinePolynomialSpan (k := k) (R := R) p hp).val =
      finiteCyclePushforward (affineSpanAmbient (k := k) (R := R) (A := A))
        (finiteCyclePushforward (inclusion p) (AlgebraicCycle.fundamentalCycle _)) := by
  let := source_finite p hp
  let := source_flat p hp
  rw [affinePolynomialSpan, Cor.ofFiniteFlatSpan_val]
  have congrPush {D E : Scheme.{u}} (l r : D ⟶ E) [IsFinite l] [IsFinite r]
      (h : l = r) (c : AlgebraicCycle D ℤ) :
      finiteCyclePushforward l c = finiteCyclePushforward r c := by
    cases h
    rfl
  exact (congrPush _ _ (affineSpanAmbient_quotient (k := k) p) _).trans
    (finiteCyclePushforward_comp_apply (inclusion p) (affineSpanAmbient (k := k) (R := R)) _).symm

/-- Multiplication adds the native spans in the same principal open. -/
theorem openPolynomialSpan_mul [IsNoetherianRing A]
    (p q : A[X]) (hp : p.Monic) (hq : q.Monic) (f : R[X])
    (hpf : IsUnit (AdjoinRoot.mk p (f.map (algebraMap R A))))
    (hqf : IsUnit (AdjoinRoot.mk q (f.map (algebraMap R A))))
    (hpqf : IsUnit (AdjoinRoot.mk (p * q) (f.map (algebraMap R A)))) :
    openPolynomialSpan (k := k) (p * q) (hp.mul hq) f hpqf =
      openPolynomialSpan (k := k) p hp f hpf + openPolynomialSpan (k := k) q hq f hqf := by
  let : IsOpenImmersion (openInclusion (k := k) f).left :=
    inferInstanceAs (IsOpenImmersion (principalOpen f).ι)
  apply PolynomialCurveCycles.openGraph_injective k (openInclusion (k := k) f)
  dsimp only
  erw [Preadditive.add_comp, openPolynomialSpan_comp_inclusion, openPolynomialSpan_comp_inclusion,
    openPolynomialSpan_comp_inclusion]
  apply Subtype.ext
  change (affinePolynomialSpan (k := k) (R := R) (p * q) (hp.mul hq)).val =
    (affinePolynomialSpan (k := k) (R := R) p hp).val +
      (affinePolynomialSpan (k := k) (R := R) q hq).val
  simp only [affinePolynomialSpan_val, quotientFundamentalCycle_mul p q hp hq, map_add]

/-- A linear quotient gives the graph of its original coordinate. -/
theorem openPolynomialSpan_linear (a : A) (f : R[X])
    (hf : IsUnit (AdjoinRoot.mk (Polynomial.X - C a) (f.map (algebraMap R A))))
    (j : U ⟶ openSite (k := k) f)
    (hj : j.left ≫ (principalOpen f).ι =
      Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (algebraMap R A) a))) :
    openPolynomialSpan (k := k) (Polynomial.X - C a) (monic_X_sub_C a) f hf =
      (Cor.graphFunctor k).map j := by
  let := source_finite (Polynomial.X - C a) (monic_X_sub_C a)
  let := source_flat (Polynomial.X - C a) (monic_X_sub_C a)
  let : IsFinite (𝟙 (U).left) := inferInstanceAs (IsFinite (𝟙 (Spec (.of A))))
  let : Flat (𝟙 (U).left) := inferInstanceAs (Flat (𝟙 (Spec (.of A))))
  rw [openPolynomialSpan, ← Cor.ofFiniteFlatSpan_id_left j]
  apply Cor.ofFiniteFlatSpan_eq_of_iso (asIso (source (Polynomial.X - C a)))
  · exact Category.comp_id _
  · apply (cancel_mono (principalOpen f).ι).mp
    rw [Category.assoc, hj, openTarget_inclusion]
    exact (target_linear (algebraMap R A) a).symm

/-- The signed corrections use the actual inclusion of the smaller open. -/
theorem openPolynomialSpan_narrow (p : A[X]) (hp : p.Monic) (f g : R[X])
    (hf : IsUnit (AdjoinRoot.mk p ((f * g).map (algebraMap R A)))) :
    openPolynomialSpan (k := k) p hp (f * g) hf ≫ (Cor.graphFunctor k).map (narrowInclusion f g) =
      openPolynomialSpan (k := k) p hp f (old_boundary_unit p f g hf) := by
  let : IsOpenImmersion (openInclusion (k := k) f).left :=
    inferInstanceAs (IsOpenImmersion (principalOpen f).ι)
  apply PolynomialCurveCycles.openGraph_injective k (openInclusion (k := k) f)
  dsimp only
  erw [Category.assoc, ← Functor.map_comp, narrowInclusion_comp, openPolynomialSpan_comp_inclusion,
    openPolynomialSpan_comp_inclusion]

end SmoothSite

end AlgebraicGeometry.PolynomialOpenQuotient
