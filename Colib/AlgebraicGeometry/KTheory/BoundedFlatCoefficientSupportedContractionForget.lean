/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedPolynomialLaurentTransport
public import Colib.AlgebraicGeometry.KTheory.Bass.SupportedForget
public import Colib.KTheory.Bass.DiagramTransportGroupNaturality

/-!
Source:
`PerfectComplexes/BoundedFlat/CoefficientSupportedContractionForget.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Original support forgetting under coefficient contraction transport

The original pair-to-ambient transport has the same geometric Laurent map as the ambient
coefficient transport. Its quotient equation and generic group-map naturality give the
actual forget-support square required by the original negative-group recursion.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme CommRingCat.PolynomialLaurent KTheory.Bass.TwoChart
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace Q.left]

/-- Forgetting the pair retains exactly the original ambient Laurent transport. -/
@[reassoc]
theorem boundedAboveFlatCoefficientSupportedContractionTransportIso_base
    (G : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (a : Under R) :
    (boundedAboveFlatCoefficientSupportedContractionTransportIso f
      (quasiCompactOpenPairsBase.op ⋙ G)).hom.app a ≫
        (Bass.supportedContractionForgetIso G).hom.app
          ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).obj a) =
      (boundedAboveFlatCoefficientContractionTransportIso Q G).hom.app a := by
  apply (cancel_epi ((contractionπ (underToLaurent R) (underToLaurentInvert R)
    (boundedAboveFlatCoefficientQuasiCompactRow Q ⋙ G)).app a)).mp
  erw [boundedAboveFlatCoefficientSupportedContractionTransportIso_π_assoc f
    (quasiCompactOpenPairsBase.op ⋙ G) a,
    boundedAboveFlatCoefficientContractionTransportIso_π Q G a]
  unfold Bass.supportedContractionForgetIso
  rw [contractionTransportIso_π]
  change G.map ((boundedAboveFlatCoefficientLaurentIso Q).hom.app a) ≫
      G.map (𝟙 _) ≫ _ = _
  rw [G.map_id, Category.id_comp]
  rfl

/-- Every original group-valued support-forgetting map retains its actual coefficient transport. -/
@[reassoc]
theorem boundedAboveFlatCoefficientSupportedContractionTransportIso_forget
    {F : QuasiCompactOpenPairs.{u}ᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
    {G : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
    (α : F ⟶ quasiCompactOpenPairsBase.op ⋙ G) (a : Under R) :
    (contractionMap (underToLaurent R) (underToLaurentInvert R)
      (Functor.whiskerLeft (boundedAboveFlatCoefficientQuasiCompactOpenPairRow f) α)).app a ≫
        (boundedAboveFlatCoefficientContractionTransportIso Q G).hom.app a =
      (boundedAboveFlatCoefficientSupportedContractionTransportIso f F).hom.app a ≫
        (contractionMap (NatTrans.op Scheme.Bass.pairPlus)
          (NatTrans.op Scheme.Bass.pairMinus) α).app
          ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).obj a) ≫
        (Bass.supportedContractionForgetIso G).hom.app
          ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).obj a) := by
  rw [← boundedAboveFlatCoefficientSupportedContractionTransportIso_base f G a,
    ← Category.assoc]
  have h := contractionTransportIso_groupMap
    (NatTrans.op Scheme.Bass.pairPlus) (NatTrans.op Scheme.Bass.pairMinus)
    (underToLaurent R) (underToLaurentInvert R)
    (boundedAboveFlatCoefficientQuasiCompactOpenPairRow f)
    (boundedAboveFlatCoefficientSupportedPolynomialIso f)
    (boundedAboveFlatCoefficientSupportedLaurentIso f)
    (boundedAboveFlatCoefficientSupportedPolynomialLaurentIso_plus f)
    (boundedAboveFlatCoefficientSupportedPolynomialLaurentIso_minus f) α a
  rw [show (contractionMap (underToLaurent R) (underToLaurentInvert R)
      (Functor.whiskerLeft (boundedAboveFlatCoefficientQuasiCompactOpenPairRow f) α)).app a ≫
        (boundedAboveFlatCoefficientSupportedContractionTransportIso f
          (quasiCompactOpenPairsBase.op ⋙ G)).hom.app a = _ from h]
  exact Category.assoc _ _ _

/-- The original recursive supported forget map commutes with the unchanged coefficient transport.
-/
theorem boundedAboveFlatCoefficientSupportedContractionTransportIso_negativeForget (i : ℕ) :
    (boundedAboveFlatCoefficientSupportedContractionTransportIso f
      (Bass.supportedNegativeKFunctor i)).hom ≫
        Functor.whiskerLeft (boundedAboveFlatCoefficientQuasiCompactOpenPairRow f)
          (Bass.supportedNegativeKForgetNat (i + 1)) =
      (contractionFunctor (underToLaurent R) (underToLaurentInvert R)).map
        (Functor.whiskerLeft (boundedAboveFlatCoefficientQuasiCompactOpenPairRow f)
          (Bass.supportedNegativeKForgetNat i)) ≫
        (boundedAboveFlatCoefficientContractionTransportIso Q (Bass.negativeKFunctor i)).hom := by
  apply NatTrans.ext
  funext a
  exact (boundedAboveFlatCoefficientSupportedContractionTransportIso_forget f
    (Bass.supportedNegativeKForgetNat i) a).symm


attribute [colib_ref "quillen" "CoefficientSupportedContractionForget.lean:32"
  "adaptation" "Original supported finite-bottom comparison and actual quotient naturality"]
  boundedAboveFlatCoefficientSupportedContractionTransportIso_base
attribute [colib_ref "quillen" "CoefficientSupportedContractionForget.lean:53"
  "adaptation" "Original supported finite-bottom comparison and actual quotient naturality"]
  boundedAboveFlatCoefficientSupportedContractionTransportIso_forget
attribute [colib_ref "quillen" "CoefficientSupportedContractionForget.lean:83"
  "adaptation" "Original supported finite-bottom comparison and actual quotient naturality"]
  boundedAboveFlatCoefficientSupportedContractionTransportIso_negativeForget

end AlgebraicGeometry.Scheme.Modules
