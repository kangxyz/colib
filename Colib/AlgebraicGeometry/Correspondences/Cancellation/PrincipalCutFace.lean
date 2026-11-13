/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.ClosedEndpointSpecialization
import Colib.AlgebraicGeometry.Chow.DoublePrincipalCut

/-!
# Principal cut coefficients along a graph face

An affine coordinate face of the smooth source restricts a native cut
correspondence by graph precomposition. If the cut is carried by a closed
support, its restricted coefficient at a common cut point is the component
cut of the actual face fibre. The whole intermediate fibre can have
embedded torsion.
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme Scheme.AffineLineFiber AlgebraicCycle Stacks.Chow

variable {k : Type u} [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  {P : Scheme.{u}} [IsNoetherian P]
  (φ : X ⟶ Y) (q : Y.left ⟶ Spec (.of (Polynomial k))) [Flat q] (a : k)
  (H : IsPullback φ.left X.hom q (point a))
  (m : P ⟶ pullback Y.hom Z.hom) [IsClosedImmersion m]

/-- The literal graph precomposition of an admissible cut, evaluated at its
actual closed face support, has the coefficient of the cut made after
restricting to the face. Finite colength and properness are local at the
specified cut point. Flatness is imposed on the smooth source coordinate
map, while the cut support and its face fibre can be nonflat. -/
theorem graph_comp_closedFiberCycle_endpoint_apply_eq_cut
    (f : P ⟶ Spec (.of (Polynomial k))) (hf : m ≫ pullback.fst Y.hom Z.hom ≫ q = f)
    (g : P ⟶ Spec (.of (Polynomial k))) (b : k)
    (α : Cor.mk Y ⟶ Cor.mk Z)
    (hα : α.val = finiteCyclePushforward m
      (finiteCyclePushforward (inclusion g b) (fundamentalCycle (fiber g b))))
    (x : fiber f a) (hx : inclusion f a x ∈ Set.range (inclusion g b))
    (hrf : IsSMulRegular (P.presheaf.stalk (inclusion f a x)) (scalar f a (inclusion f a x)))
    (hrg : IsSMulRegular (P.presheaf.stalk (inclusion f a x)) (scalar g b (inclusion f a x)))
    (hfin : Module.length (P.presheaf.stalk (inclusion f a x))
      (P.presheaf.stalk (inclusion f a x) ⧸
        (Ideal.span {scalar f a (inclusion f a x)} ⊔
          Ideal.span {scalar g b (inclusion f a x)})) ≠ ⊤)
    (hproperf : ∀ r : PrimeSpectrum (P.presheaf.stalk (inclusion f a x)),
      r.asIdeal ∈ (Ideal.span {scalar g b (inclusion f a x)}).minimalPrimes →
        scalar f a (inclusion f a x) ∉ r.asIdeal)
    (hproperg : ∀ r : PrimeSpectrum (P.presheaf.stalk (inclusion f a x)),
      r.asIdeal ∈ (Ideal.span {scalar f a (inclusion f a x)}).minimalPrimes →
        scalar g b (inclusion f a x) ∉ r.asIdeal) :
    ((graphFunctor k).map φ ≫ α).val
        (closedSupportEndpointMapOfParameterEq φ q a H m f hf x) =
      finiteCyclePushforward (inclusion (inclusion f a ≫ g) b)
        (polynomialEndpointMap (inclusion f a ≫ g) b (fundamentalCycle (fiber f a))) x := by
  let e : fiber f a ⟶ pullback X.hom Z.hom :=
    closedSupportEndpointMapOfParameterEq φ q a H m f hf
  let c := polynomialEndpointMap f a
    (finiteCyclePushforward (inclusion g b) (fundamentalCycle (fiber g b)))
  calc
    _ = finiteCyclePushforward e c (e x) :=
      DFunLike.congr_fun (graph_comp_closedCycle_endpoint_of_parameter_eq
        φ q a H m f hf _ α hα) (e x)
    _ = c x := finiteCyclePushforward_apply_of_isClosedImmersion e c x
    _ = _ := polynomialEndpointMap_fundamentalFiber_apply_eq_cut f g a b x hx hrf hrg
      hfin hproperf hproperg

end AlgebraicGeometry.Cor
