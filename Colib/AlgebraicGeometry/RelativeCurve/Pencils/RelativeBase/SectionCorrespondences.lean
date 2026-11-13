/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.RelativeSupport
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.GeneratedDivisors

/-! # Native correspondences of the two prescribed section pairs

The two differences use the whole zero schemes of the sections already stored
in `SectionData`. Both legs of each finite-flat span are the projections of the
actual retained product. The numerator and denominator retain their original
order in the signed pencil.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Ample Stacks.Divisors
open Stacks.Chow

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

attribute [local instance] compactificationGraphIdeal_isEffectiveCartierDivisor

local instance (X : Scheme.{u}) (M : X.Modules) [hM : IsInvertibleModule X M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M :=
  hM

variable {S X C Y A Z D : Scheme.{u}}
  {q : X ⟶ S} [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  {π : C ⟶ S} [IsProper π]
  {j : Y ⟶ C} [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  {p : Y ⟶ X} {hq : j ≫ π = p ≫ q} {a : A ⟶ X}
  {z : Z ⟶ X} {s : Z ⟶ Y} {hs : s ≫ p = z} {H : IsPullback s (𝟙 Z) p z}
  {e : divisorSheaf (relativeBoundaryGraph q z).ker ≅
    SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf}
  {d : D ⟶ C} {hd : Disjoint (Set.range j) (Set.range d)}
  {ha : Disjoint (Set.range a) (Set.range z)}

namespace SectionData

variable (c : SectionData q π j p hq a z s hs H e d hd ha)
  {k : Type u} [Field k] (t : S ⟶ Spec (.of k)) [Smooth t]
  [IsAffine S] [IsAffine Y] [IsAffine A]
  {V : Scheme.{u}} [IsAffine V] (v : V ⟶ C) [IsOpenImmersion v]
  [SmoothOfRelativeDimension 1 (v ≫ π)]
  (hc : ∀ x : C, x ∈ Set.range v ∨ x ∈ Set.range d ∨ x ∈ Set.range (s ≫ j))

local instance : Smooth (j ≫ π) := SmoothOfRelativeDimension.smooth 1 (j ≫ π)
local instance : Smooth (v ≫ π) := SmoothOfRelativeDimension.smooth 1 (v ≫ π)
local instance : Smooth q := SmoothOfRelativeDimension.smooth 1 q

local notation "F" => divisorSheaf (Scheme.Hom.ker (compactificationGraph π j))
local notation "rA" => retainedProductInclusion (j ≫ π) π v
local notation "rN" => retainedProductInclusion (a ≫ q) π v
local notation "rV" => v ≫ π

/-- The first-source correspondence is the actual numerator span minus the pole span. -/
def lambda : finiteCorrespondences ((j ≫ π) ≫ t) (rV ≫ t) :=
  letI := c.T_invertible
  letI : IsInvertibleModule (pullback (j ≫ π) π) (tensorModules F c.T) :=
    @Stacks.Chow.TensorZeroScheme.isInvertible_tensorSheaf (pullback (j ≫ π) π) F c.T
      (inferInstanceAs (IsInvertibleModule (pullback (j ≫ π) π) F)) c.T_invertible
  let IA := (zeroScheme _ (tensorModules F c.T) c.aS).comap rA
  let IB := (zeroScheme _ c.T c.bS).comap rA
  let hAB := c.retainedFirstFactors_comap_finite_relativeCartier v hc
  letI : IsNoetherian Y := isNoetherian_of_finiteType_of_isNoetherian ((j ≫ π) ≫ t)
  letI : IsAffineHom (rV ≫ t) := isAffineHom_of_isAffine _
  Cor.ofFiniteFlatSpanRaw ((j ≫ π) ≫ t) (rV ≫ t)
      (IA.subschemeι ≫ pullback.fst (j ≫ π) rV) (IA.subschemeι ≫ pullback.snd (j ≫ π) rV)
      (hFin := hAB.1.1) (hFlat := hAB.1.2.2)
      (Cor.relativeSupport_legs_over_base (j ≫ π) rV t IA) -
    Cor.ofFiniteFlatSpanRaw ((j ≫ π) ≫ t) (rV ≫ t)
      (IB.subschemeι ≫ pullback.fst (j ≫ π) rV) (IB.subschemeι ≫ pullback.snd (j ≫ π) rV)
      (hFin := hAB.2.1) (hFlat := hAB.2.2.2)
      (Cor.relativeSupport_legs_over_base (j ≫ π) rV t IB)

variable [IsOpenImmersion a]

/-- The correction is the actual denominator span minus the numerator span. -/
def psi : finiteCorrespondences ((a ≫ q) ≫ t) (rV ≫ t) :=
  letI := c.N_invertible
  let IN := (zeroScheme _ c.N c.nS).comap rN
  let ID := (zeroScheme _ c.N c.dS).comap rN
  let hND := c.retainedCorrectionFactors_comap_finite_relativeCartier v hc
  letI : IsNoetherian A := isNoetherian_of_finiteType_of_isNoetherian ((a ≫ q) ≫ t)
  letI : IsAffineHom (rV ≫ t) := isAffineHom_of_isAffine _
  Cor.ofFiniteFlatSpanRaw ((a ≫ q) ≫ t) (rV ≫ t)
      (ID.subschemeι ≫ pullback.fst (a ≫ q) rV) (ID.subschemeι ≫ pullback.snd (a ≫ q) rV)
      (hFin := hND.2.1) (hFlat := hND.2.2.2)
      (Cor.relativeSupport_legs_over_base (a ≫ q) rV t ID) -
    Cor.ofFiniteFlatSpanRaw ((a ≫ q) ≫ t) (rV ≫ t)
      (IN.subschemeι ≫ pullback.fst (a ≫ q) rV) (IN.subschemeι ≫ pullback.snd (a ≫ q) rV)
      (hFin := hND.1.1) (hFlat := hND.1.2.2)
      (Cor.relativeSupport_legs_over_base (a ≫ q) rV t IN)

end SectionData

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
