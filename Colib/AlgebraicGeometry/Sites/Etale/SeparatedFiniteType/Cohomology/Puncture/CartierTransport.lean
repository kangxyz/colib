/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.StrictA1.Basic
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Cylinder.EtaleRestriction
public import Colib.AlgebraicGeometry.Sites.Smooth.Cartier.CylinderComplement
public import Colib.AlgebraicGeometry.Sites.Smooth.Cartier.MarkedCylinderComparison
public import Colib.AlgebraicGeometry.Sites.Smooth.Cohomology.GenericOpen

/-! # Marked Cartier puncture restriction from its native cylinder charts

The étale restriction comparison transports monicity from the chart with
the same field-valued marking, full zero section and literal Laurent complement.

Adapted from `Motivic/Cohomology/A1/Cartier/Restriction/H1RestrictionMono.lean`
and `Motivic/Cohomology/A1/Cartier/Restriction/PositiveRestriction.lean`
at `a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.FreeYonedaUnivLE

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

open SmoothSite.Contraction

variable {k : Type u} [Field k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Monicity of ordinary cohomological restriction from the marked cylinder to
the puncture complementary to a smooth effective Cartier divisor. -/
def SmoothCartierPunctureRestrictionMono (F : SheafWithTransfers.{u + 1} k)
    (n : ℕ) : Prop :=
  ∀ (Y : SmoothSite (Spec (.of k))) (K : Type u) [Field K]
    (b : Spec (.of K) ⟶ Y.left) (p : Spec (.of K))
    (Z : Scheme.{u}) (i : Z ⟶ Y.left),
    IsClosedImmersion i → Stacks.Divisors.IsEffectiveCartierDivisor i.ker →
    Smooth (i ≫ Y.hom) → b p ∈ Set.range i →
    ∀ W : Y.left.Opens, Set.range i = (W : Set Y.left)ᶜ →
      Mono (colim.map (pointedCylinderRestriction (.of k)
        (SmoothSite.openInclusion Y W) (relativeFieldPoint b K (𝟙 _))
        (cohomologyPresheaf.{u + 1, u + 1} ((SheafWithTransfers.toSheaf k).obj F) n)))

/-- Monicity on the actual étale cylinder charts gives monicity at every full
Cartier marking. Pullback preserves the entire map from Spec K. -/
theorem smoothCartierPunctureRestrictionMono_of_cylinder_charts
    (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    (hChart : let P := cohomologyPresheaf.{u + 1, u + 1} ((SheafWithTransfers.toSheaf k).obj F) n
      ∀ (D E W : SmoothSite (Spec (.of k))) (q : E ⟶ affineLineCylinder.obj D)
        [Etale q.left] (d : D ⟶ E) (w : W ⟶ E) [IsOpenImmersion w.left]
        (t : W ⟶ torusCylinder.obj D),
        IsPullback d (𝟙 D) q (nativeAffineSection (.of k) D 0) →
        IsPullback t w (openInclusion.app D) q →
        ∀ (K : Type u) [Field K] (c : Spec (.of K) ⟶ D.left),
          Mono (colim.map (pointedCylinderRestriction (.of k) w
            (relativeFieldPoint (c ≫ d.left) K (𝟙 _)) P))) :
    SmoothCartierPunctureRestrictionMono F n := by
  intro Y K _ b p Z i hi hI hs hb W hW
  let : IsClosedImmersion i := hi
  let : Smooth (i ≫ Y.hom) := hs
  let j := SmoothSite.openInclusion Y W
  let : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion W.ι)
  have hp : (IsLocalRing.closedPoint K : PrimeSpectrum K) = p := Subsingleton.elim _ _
  obtain ⟨O, E, a, q, d, c, ha, hq, hpa, hpq, hbE⟩ :=
    SmoothSite.exists_marked_cartier_cylinder_comparison Y i hI K b (hp.symm ▸ hb)
  let D := SmoothSite.closedOpenSite (Y := Y) i O
  let : Etale a.left := ha
  let : Etale q.left := hq
  have hd : IsPullback d (𝟙 D) q (nativeAffineSection (.of k) D 0) :=
    IsPullback.of_map_of_faithful (SmoothSite.forgetScheme (Spec (.of k))) hpq
  have hcomp : Set.range i = (Set.range j.left)ᶜ := by
    change Set.range i = (Set.range W.ι)ᶜ
    rwa [Scheme.Opens.range_ι]
  obtain ⟨hA, t, hB⟩ := exists_native_cartier_puncture_comparison (.of k) j a q d i O.ι
    hpa hpq hcomp
  let w := SmoothSite.etalePullbackSnd j a
  let : IsOpenImmersion w.left := inferInstanceAs (IsOpenImmersion (pullback.snd j.left a.left))
  let := hChart D E _ q d w t hd hB K c
  let P := cohomologyPresheaf.{u + 1, u + 1} ((SheafWithTransfers.toSheaf k).obj F) n
  let M (g : Spec (.of K) ⟶ Y.left) : Prop :=
    Mono (colim.map (pointedCylinderRestriction (.of k) j (relativeFieldPoint g K (𝟙 _)) P))
  change M b
  have h : M ((c ≫ d.left) ≫ a.left) :=
    fieldPoint_cylinderRestriction_mono_of_etale (.of k) P j a w
      (SmoothSite.etalePullbackFst j a) hA K (c ≫ d.left)
  exact hbE ▸ h

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
