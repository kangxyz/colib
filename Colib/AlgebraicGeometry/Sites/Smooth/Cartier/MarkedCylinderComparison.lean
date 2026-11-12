/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Cartier.CylinderComparison
public import Colib.AlgebraicGeometry.Sites.Nisnevich.Lifting.DistinguishedSquare

/-!
# Cartier cylinder charts retaining the complete field-valued mark

Extracted from the geometric part of motivic a6805c4a87cdfd7717dd7a94039246a167f15380,
Motivic/Cohomology/A1/Cartier/Restriction/H1RestrictionMono.lean,
blob 8f0212401a0451252633d0572cc2f9dcaacfab29.
All lifts retain the entire Spec K morphism and the same field K.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite

/-- An actual smooth Cartier pair admits its native cylinder chart at an unchanged full-K mark. -/
theorem exists_marked_cartier_cylinder_comparison
    {k : Type u} [Field k] (Y : SmoothSite (Spec (.of k)))
    {Z : Scheme.{u}} (i : Z ⟶ Y.left) [IsClosedImmersion i] [Smooth (i ≫ Y.hom)]
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor i.ker)
    (K : Type u) [Field K] (b : Spec (.of K) ⟶ Y.left)
    (hb : b (IsLocalRing.closedPoint K) ∈ Set.range i) :
    ∃ (O : Z.Opens) (V : SmoothSite (Spec (.of k))) (a : V ⟶ Y)
      (q : V ⟶ Contraction.affineLineCylinder.obj (closedOpenSite (Y := Y) i O))
      (d : closedOpenSite (Y := Y) i O ⟶ V)
      (c : Spec (.of K) ⟶ (closedOpenSite (Y := Y) i O).left),
      Etale a.left ∧ Etale q.left ∧
      IsPullback d.left O.ι a.left i ∧
      IsPullback d.left (𝟙 _) q.left
        (Contraction.nativeAffineSection (.of k) (closedOpenSite (Y := Y) i O) 0).left ∧
      (c ≫ d.left) ≫ a.left = b := by
  obtain ⟨cZ, hcZ⟩ := Scheme.exists_field_lift_of_mem_range i b hb
  obtain ⟨O, hO, V, a, q, d, ha, hq, hpa, hpq⟩ :=
    exists_cartier_cylinder_comparison Y i hI (cZ (IsLocalRing.closedPoint K))
  obtain ⟨c, hc⟩ := Scheme.exists_field_lift_of_mem_range O.ι cZ (by
    rw [Scheme.Opens.range_ι]
    exact hO)
  refine ⟨O, V, a, q, d, c, ha, hq, hpa, hpq, ?_⟩
  let d₀ : O.toScheme ⟶ V.left := d.left
  have h : d₀ ≫ a.left = O.ι ≫ i := hpa.w
  change (c ≫ d₀) ≫ a.left = b
  exact (Category.assoc c d₀ a.left).trans
    ((congrArg (fun f => c ≫ f) h).trans
      ((Category.assoc c O.ι i).symm.trans ((congrArg (fun f => f ≫ i) hc).trans hcZ)))

end AlgebraicGeometry.Scheme.SmoothSite
