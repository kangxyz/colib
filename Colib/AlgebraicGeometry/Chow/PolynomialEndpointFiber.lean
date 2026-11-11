/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.FiniteFlatProduct
public import Colib.Util.References
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Polynomial.Ideal
public import StacksFrontier.AlgebraicGeometry.Chow.LocalEquationMultiplicity
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.IntegralSchemes
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk

/-!
# Native cycle coefficients of polynomial endpoint fibers

The kernel ideal of the whole scheme-theoretic endpoint fiber has the literal
equation `X - C a` in each ambient stalk. For an integral finite flat family,
the native pushed fundamental coefficient is the order of that equation at
each codimension-one point, with the full length of the stalk quotient.

The stalk calculation is adapted from Motivic at
`a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Aglib/AlgebraicGeometry/RelativeCurve/Endpoints/FiniteFlatCurveSpecialization.lean:92-155`.
The order comparison uses `Stacks.Chow.ord_eq_ringOrd_germ` from
`StacksFrontier/AlgebraicGeometry/Chow/LocalEquationMultiplicity.lean` at
`5ed82d14634e8d9576bb844c7bd4e3da66d450e7`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped Polynomial

universe u

namespace Stacks.Chow.PolynomialEndpointFiber

variable {k : Type u} [Field k] {P : Scheme.{u}}

/-- The field point of the affine line with polynomial coordinate `a`. -/
abbrev endpoint (a : k) : Spec (.of k) ⟶ Spec (.of k[X]) :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))

instance endpoint_isClosedImmersion (a : k) : IsClosedImmersion (endpoint a) :=
  IsClosedImmersion.spec_of_surjective _ (Polynomial.eval_surjective a)

variable (f : P ⟶ Spec (.of k[X])) (a : k)

/-- The whole scheme-theoretic endpoint fiber. -/
abbrev fiber : Scheme.{u} := pullback (endpoint a) f

/-- The actual endpoint-fiber inclusion in the family. -/
abbrev fiberInclusion : fiber f a ⟶ P := pullback.snd (endpoint a) f

/-- A finite family has Noetherian endpoint fibers. -/
theorem fiber_isNoetherian [IsFinite f] : IsNoetherian (fiber f a) :=
  { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (pullback.fst (endpoint a) f)
    toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (pullback.fst (endpoint a) f) }

private def baseEquation : Γ(Spec (.of k[X]), ⊤) :=
  (Scheme.ΓSpecIso (.of k[X])).inv (Polynomial.X - Polynomial.C a)

/-- The actual pullback of the endpoint equation as a global section. -/
def equation : Γ(P, ⊤) :=
  f.appTop ((Scheme.ΓSpecIso (.of k[X])).inv (Polynomial.X - Polynomial.C a))

private theorem endpoint_ker_top :
    (endpoint a).ker.ideal ⟨⊤, isAffineOpen_top _⟩ =
      (Ideal.span {Polynomial.X - Polynomial.C a}).map (Scheme.ΓSpecIso (.of k[X])).inv.hom := by
  rw [Scheme.Hom.ker_apply, ← Polynomial.ker_evalRingHom]
  change RingHom.ker (endpoint a).appTop.hom = _
  rw [← RingHom.ker_equiv_comp _ (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv]
  change RingHom.ker ((Scheme.ΓSpecIso (.of k)).hom.hom.comp (endpoint a).appTop.hom) = _
  rw [← CommRingCat.hom_comp, Scheme.ΓSpecIso_naturality, CommRingCat.hom_comp, ← RingHom.comap_ker]
  exact (Ideal.map_symm (Scheme.ΓSpecIso (.of k[X])).commRingCatIsoToRingEquiv).symm

private theorem endpoint_ker_stalk (x : Spec (.of k[X])) :
    IdealSheafData.stalk (endpoint a).ker x =
      Ideal.span {(Spec (.of k[X])).presheaf.germ ⊤ x trivial (baseEquation a)} := by
  rw [IdealSheafData.stalk_eq_map_germ _ x ⟨⊤, isAffineOpen_top _⟩ trivial,
    endpoint_ker_top, Ideal.map_map, Ideal.map_span, Set.image_singleton]
  rfl

/-- The full defining ideal of the endpoint fiber is principal in the ambient stalk. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/RelativeCurve/Endpoints/\
    FiniteFlatCurveSpecialization.lean:92-155"
  "adaptation" "The original endpoint equation in the kernel stalk of the native fiber inclusion"]
theorem fiberInclusion_ker_stalk (x : P) :
    IdealSheafData.stalk (fiberInclusion f a).ker x =
      Ideal.span {P.presheaf.germ ⊤ x trivial (equation f a)} := by
  have hker : (fiberInclusion f a).ker = (endpoint a).ker.comap f := by
    calc
      _ = ((pullbackSymmetry f (endpoint a)).hom ≫ fiberInclusion f a).ker :=
        (Scheme.Hom.ker_comp_of_isIso _ _).symm
      _ = (pullback.fst f (endpoint a)).ker := by rw [fiberInclusion, pullbackSymmetry_hom_comp_snd]
      _ = _ := Scheme.IdealSheafData.ker_fst_of_isClosedImmersion _ _
  have hgerm : f.stalkMap x ((Spec (.of k[X])).presheaf.germ ⊤ (f x) trivial (baseEquation a)) =
      P.presheaf.germ ⊤ x trivial (equation f a) :=
    Scheme.Hom.germ_stalkMap_apply f ⊤ x trivial (baseEquation a)
  rw [hker, IdealSheafData.stalk_comap, endpoint_ker_stalk, Ideal.map_span, Set.image_singleton]
  exact congrArg (fun t => Ideal.span {t}) hgerm

private abbrev affineLineToPoint (k : Type u) [Field k] : Spec (.of k[X]) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))

private theorem endpoint_comp_affineLineToPoint : endpoint a ≫ affineLineToPoint k = 𝟙 _ := by
  have he : CommRingCat.ofHom (Polynomial.C : k →+* k[X]) ≫
      CommRingCat.ofHom (Polynomial.evalRingHom a) = 𝟙 (CommRingCat.of k) := by
    ext b
    simp
  rw [endpoint, affineLineToPoint, ← Spec.map_comp, he, Spec.map_id]

private theorem fiberInclusion_comp_affineLineToPoint :
    fiberInclusion f a ≫ (f ≫ affineLineToPoint k) = pullback.fst (endpoint a) f := by
  calc
    _ = pullback.fst (endpoint a) f ≫ (endpoint a ≫ affineLineToPoint k) := by
      simp only [← Category.assoc, fiberInclusion, pullback.condition]
    _ = _ := by rw [endpoint_comp_affineLineToPoint, Category.comp_id]

variable [IsIntegral P]

/-- The endpoint equation viewed in the function field of the family. -/
def rationalFunction : P.functionField := by
  letI : Nonempty ((⊤ : P.Opens) : Type u) := ⟨⟨genericPoint P, trivial⟩⟩
  exact P.germToFunctionField ⊤ (equation f a)

private theorem equation_ne_zero [IsFinite f] [Flat f] : equation f a ≠ 0 := by
  have hη : genericPoint P ∈ genericPoints P := by simp [genericPoints_eq_singleton]
  have h := mem_genericPoints_of_flat f hη
  let : IsDominant f := ((tfae_isDominant_of_isIntegral f).out 1 2).mpr (by
    simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using h)
  let : IsSchemeTheoreticallyDominant f := IsSchemeTheoreticallyDominant.of_isDominant f
  have happ : Function.Injective f.appTop.hom := f.app_injective ⊤
  have hinv : Function.Injective (Scheme.ΓSpecIso (.of k[X])).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k[X])).inv).1
  intro hz
  change f.appTop.hom
    ((Scheme.ΓSpecIso (.of k[X])).inv.hom (Polynomial.X - Polynomial.C a)) = 0 at hz
  have hzero : f.appTop.hom ((Scheme.ΓSpecIso (.of k[X])).inv.hom 0) = 0 := by
    simp only [map_zero]
  exact Polynomial.X_sub_C_ne_zero a (hinv (happ (hz.trans hzero.symm)))

/-- The endpoint equation is nonzero on a finite flat integral family. -/
theorem rationalFunction_ne_zero [IsFinite f] [Flat f] : rationalFunction f a ≠ 0 := by
  let : Nonempty ((⊤ : P.Opens) : Type u) := ⟨⟨genericPoint P, trivial⟩⟩
  exact (map_ne_zero_iff _ (P.germToFunctionField_injective ⊤)).mpr (equation_ne_zero f a)

/-- The pushed full endpoint cycle reads as the order of its equation at every height-one point. -/
theorem finiteCyclePushforward_fundamentalCycle_apply_eq_ord [IsFinite f] [Flat f]
    (x : P) (hx : Order.coheight x = 1) :
    letI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian f
    letI : IsNoetherian (fiber f a) := fiber_isNoetherian f a
    finiteCyclePushforward (fiberInclusion f a) (AlgebraicCycle.fundamentalCycle (fiber f a)) x =
      P.ord (rationalFunction f a) x := by
  let : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsNoetherian (fiber f a) := fiber_isNoetherian f a
  let : Nonempty ((⊤ : P.Opens) : Type u) := ⟨⟨genericPoint P, trivial⟩⟩
  let p := f ≫ affineLineToPoint k
  let : IsFinite (fiberInclusion f a ≫ p) := by
    change IsFinite (fiberInclusion f a ≫ (f ≫ affineLineToPoint k))
    rw [fiberInclusion_comp_affineLineToPoint]
    infer_instance
  have hpx : p x ∈ genericPoints (Spec (.of k)) := by
    rw [genericPoints_eq_singleton, Set.mem_singleton_iff]
    exact Subsingleton.elim _ _
  have hlen := closedImmersionQuotientStalkLength_ne_top p (fiberInclusion f a) x hpx
  have hord : Ring.ord (P.presheaf.stalk x) (P.presheaf.germ ⊤ x trivial (equation f a)) =
      ((closedImmersionQuotientStalkLength (fiberInclusion f a) x).toNat : ℕ∞) := by
    rw [ENat.natCast_toNat hlen, Ring.ord, closedImmersionQuotientStalkLength,
      fiberInclusion_ker_stalk]
  rw [finiteCyclePushforward_fundamentalCycle_apply_eq_quotientStalkLength
    p (fiberInclusion f a) x hpx]
  exact (ord_eq_ringOrd_germ (V := ⊤) hx trivial (equation f a) (equation_ne_zero f a) hord).symm

end Stacks.Chow.PolynomialEndpointFiber
