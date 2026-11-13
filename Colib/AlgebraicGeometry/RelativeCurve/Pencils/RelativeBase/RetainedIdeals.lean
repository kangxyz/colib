/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.GeneratedIdeals
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RetainedGeneratedGraph
/-! # Literal retained zero ideals over the general relative base -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Ample Stacks.Divisors
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
attribute [local instance] compactificationGraphIdeal_isEffectiveCartierDivisor

local instance (X : Scheme.{u}) (M : X.Modules) [hM : IsInvertibleModule X M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M := hM

variable {S X C Y A B Z D : Scheme.{u}}
  {q : X ⟶ S} [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  {π : C ⟶ S} [IsSeparated π]
  {j : Y ⟶ C} [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  {p : Y ⟶ X} {hq : j ≫ π = p ≫ q} {a : A ⟶ X}
  {z : Z ⟶ X} {s : Z ⟶ Y} {hs : s ≫ p = z} {H : IsPullback s (𝟙 Z) p z}
  {e : divisorSheaf (relativeBoundaryGraph q z).ker ≅
    SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf}
  {d : D ⟶ C} {hd : Disjoint (Set.range j) (Set.range d)}
  {ha : Disjoint (Set.range a) (Set.range z)}

variable (α : B ⟶ Y) (β : B ⟶ A) (h : α ≫ p = β ≫ a)
local notation "XA" => pullback (j ≫ π) π
local notation "F" => divisorSheaf (Scheme.Hom.ker (compactificationGraph π j))
local notation "σ" => divisorSheafGlobalSection (Scheme.Hom.ker (compactificationGraph π j))
local notation "gA" => commonToLambda π j α
local notation "gN" => commonToPsi (q) π j p hq a α β h
local notation "iA" => fullGraphBoundaryMap π j s d
local notation "iN" => psiBoundaryInclusion (q) π j p hq a
  (z) s hs d
local notation "i" => commonBoundaryInclusion π j α s d
local notation "qB" => commonProjection π j α

variable {V : Scheme.{u}} (v : V ⟶ C) [IsOpenImmersion v]
  (φ : B ⟶ V) (hφ : φ ≫ v = α ≫ j)

local notation "rB" => retainedProductInclusion qB π v
local notation "rA" => retainedProductInclusion (j ≫ π) π v
local notation "rN" => retainedProductInclusion (a ≫ q) π v
local notation "jA" => retainedSourceChange (j ≫ π) qB (v ≫ π) α rfl
local notation "jN" => retainedSourceChange (a ≫ q) qB (v ≫ π) β
  (Eq.symm (commonProjection_fixed q π j p hq a α β h))
local notation "G" => relativeGraphIdeal qB (v ≫ π) φ (retainedTarget_base π v j α φ hφ)

namespace SectionData

variable (c : SectionData q π j p hq a z s hs H e d hd ha)

omit [IsOpenImmersion v] in
/-- The actual retained numerator endpoint, on the unchanged two sources. -/
theorem retainedEnd_zeroScheme :
    letI := c.T_invertible
    letI := c.N_invertible
    letI : IsInvertibleModule XA (tensorModules F c.T) :=
      @Stacks.Chow.TensorZeroScheme.isInvertible_tensorSheaf XA F c.T
        (inferInstanceAs (IsInvertibleModule XA F)) c.T_invertible
    @AlgebraicGeometry.zeroScheme _ ((Modules.pullback rB).obj (c.commonLine α β h))
      (c.commonLine_pullback_invertible α β h rB)
      (pullbackGlobalSections rB _ (c.commonEnd α β h)) =
      ((zeroScheme _ (tensorModules F c.T) c.aS).comap rA).comap jA *
        ((zeroScheme _ c.N c.nS).comap rN).comap jN := by
  let := c.T_invertible
  let := c.N_invertible
  let := c.commonLine_invertible α β h
  let : IsInvertibleModule XA (tensorModules F c.T) :=
    @Stacks.Chow.TensorZeroScheme.isInvertible_tensorSheaf XA F c.T
      (inferInstanceAs (IsInvertibleModule XA F)) c.T_invertible
  let IA := zeroScheme _ (tensorModules F c.T) c.aS
  let IN := zeroScheme _ c.N c.nS
  have hPull := zeroScheme_pullback rB (c.commonLine α β h) (c.commonEnd α β h)
  have hFactors := congrArg (fun I : (commonAmbient π j α).IdealSheafData => I.comap rB)
    (c.commonEnd_zeroScheme α β h)
  have hA := retainedSourceChange_restrict_ideal (j ≫ π) qB π α rfl v IA
  have hN := retainedSourceChange_restrict_ideal (a ≫ q) qB π β
    (commonProjection_fixed q π j p hq a α β h).symm v IN
  exact hPull.trans (hFactors.trans
    ((Stacks.IdealSheaf.comap_mul (IA.comap gA) (IN.comap gN) rB).trans
      (congrArg₂ (· * ·) hA hN)))

omit [IsOpenImmersion v] in
/-- The complete retained constant pole, with the same two source maps. -/
theorem retainedPole_zeroScheme : letI := c.T_invertible; letI := c.N_invertible
    @AlgebraicGeometry.zeroScheme _ ((Modules.pullback rB).obj (c.commonPoleLine α β h))
      (c.commonPoleLine_pullback_invertible α β h rB)
      (pullbackGlobalSections rB _ (c.commonPole α β h)) =
      ((zeroScheme _ c.T c.bS).comap rA).comap jA *
        ((zeroScheme _ c.N c.dS).comap rN).comap jN := by
  let := c.T_invertible
  let := c.N_invertible
  let := c.commonPoleLine_invertible α β h
  let IA := zeroScheme _ c.T c.bS
  let IN := zeroScheme _ c.N c.dS
  have hPull := zeroScheme_pullback rB (c.commonPoleLine α β h) (c.commonPole α β h)
  have hFactors := congrArg (fun I : (commonAmbient π j α).IdealSheafData => I.comap rB)
    (c.commonPole_zeroScheme α β h)
  have hA := retainedSourceChange_restrict_ideal (j ≫ π) qB π α rfl v IA
  have hN := retainedSourceChange_restrict_ideal (a ≫ q) qB π β
    (commonProjection_fixed q π j p hq a α β h).symm v IN
  exact hPull.trans (hFactors.trans
    ((Stacks.IdealSheaf.comap_mul (IA.comap gA) (IN.comap gN) rB).trans
      (congrArg₂ (· * ·) hA hN)))

/-- The literal start is the actual retained graph times the full actual pole.
All identifications are scheme-theoretic, before passing to finite cycles. -/
theorem retainedStart_zeroScheme : letI := c.T_invertible; letI := c.N_invertible
    @AlgebraicGeometry.zeroScheme _ ((Modules.pullback rB).obj (c.commonLine α β h))
      (c.commonLine_pullback_invertible α β h rB)
      (pullbackGlobalSections rB _ (c.commonStart α β h)) =
      G * @AlgebraicGeometry.zeroScheme _ ((Modules.pullback rB).obj (c.commonPoleLine α β h))
      (c.commonPoleLine_pullback_invertible α β h rB)
        (pullbackGlobalSections rB _ (c.commonPole α β h)) := by
  let := c.T_invertible
  let := c.N_invertible
  let := c.commonLine_invertible α β h
  let := c.commonPoleLine_invertible α β h
  let : IsInvertibleModule XA (tensorModules F c.T) :=
    @Stacks.Chow.TensorZeroScheme.isInvertible_tensorSheaf XA F c.T
      (inferInstanceAs (IsInvertibleModule XA F)) c.T_invertible
  let J := (compactificationGraph π j).ker.comap gA
  let IA := (zeroScheme _ c.T c.bS).comap gA
  let IN := (zeroScheme _ c.N c.dS).comap gN
  let P := zeroScheme _ (c.commonPoleLine α β h) (c.commonPole α β h)
  have hStart : zeroScheme _ (c.commonLine α β h) (c.commonStart α β h) = J * P :=
    (c.commonStart_zeroScheme α β h).trans
      ((mul_assoc J IA IN).trans
        (congrArg (fun I : (commonAmbient π j α).IdealSheafData => J * I)
          (c.commonPole_zeroScheme α β h).symm))
  have hPull := zeroScheme_pullback rB (c.commonLine α β h) (c.commonStart α β h)
  have hFactors := congrArg (fun I : (commonAmbient π j α).IdealSheafData => I.comap rB) hStart
  have hGraph := retainedGraph_compactification_ideal π v j α φ hφ
  have hPole := zeroScheme_pullback rB (c.commonPoleLine α β h) (c.commonPole α β h)
  exact hPull.trans (hFactors.trans
    ((Stacks.IdealSheaf.comap_mul J P rB).trans (congrArg₂ (· * ·) hGraph hPole.symm)))

end SectionData

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
