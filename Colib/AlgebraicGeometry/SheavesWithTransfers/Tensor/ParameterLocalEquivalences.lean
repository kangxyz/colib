/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Functor.LocalEquivalenceOfHomEquiv
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.ParameterSections

/-!
# Represented parameter tensor preserves Nisnevich local equivalences

The proof uses the actual additive parameter adjunction and the fact that its
right adjoint preserves Nisnevich sheaves. There is no homotopy-invariance,
perfectness or flatness assumption. The temporary high import owns the existing
ordinary `parameterSectionsOfGraphIso`; move that block to its lower owner before
final integration rather than duplicate it here.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable {k : Type u} [Field k]
  {T : SmoothSite (Spec (.of k))} {F : Cor k ⥤ Cor k} [F.Additive]
  (e : Cor.graphFunctor k ⋙ F ≅
    SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k)

/-- Reindexing the original transfer coefficients commutes with inclusion. -/
def parameterSectionsUnderlyingIso :
    forget k ⋙ additivePrecompose F ≅ parameterSectionsOfGraphIso e ⋙ forget k :=
  Iso.refl _

/-- The right adjoint of the sheafified represented tensor takes values in NST. -/
def parameterPushforwardSheafificationAdjunction :
    coendPushforward F ⋙ nisnevichSheafify k ⊣
      parameterSectionsOfGraphIso e ⋙ forget k :=
  ((coendPushforwardAdjunction F).comp (nisnevichSheafificationAdjunction k)).ofNatIsoRight
    (parameterSectionsUnderlyingIso e)

include e in
/-- A represented parameter tensor preserves the morphisms inverted by actual
Nisnevich sheafification. -/
theorem isIso_sheafify_parameterPushforward_map
    {P Q : PresheafWithTransfers.{u + 1} k} (f : P ⟶ Q)
    [IsIso ((nisnevichSheafify k).map f)] :
    IsIso ((nisnevichSheafify k).map ((coendPushforward F).map f)) := by
  exact (nisnevichSheafificationAdjunction k).isIso_map_of_isIso_leftAdjoint_map
    (parameterPushforwardSheafificationAdjunction e) f

end AlgebraicGeometry.SheafWithTransfers
