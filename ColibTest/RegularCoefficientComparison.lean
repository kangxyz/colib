module

import Colib.Topology.LocalCoefficients.RegularIsomorphism

open CategoryTheory FundamentalGroupoid.LocalCoefficients
universe u
noncomputable section
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

example (b : X) (g h : FundamentalGroup X b) (z : ℤ) :
    (regularMonodromy b g).asHom (regularSingle b h.asHom z) = regularSingle b (g * h).asHom z :=
  regularMonodromy_single b g h z

example (b : X) : Function.Injective (regularMonodromy b) := regularMonodromy_injective b

example (b : X) (n : SimplexCategory) (s : RegularSimplex b n) (z : ℤ) :
    (regularBasisIso b n).hom (regularChainGenerator b s z) = Finsupp.single s z :=
  regularBasisHom_generator b s z

example (b : X) {m n : SimplexCategory} (s : RegularSimplex b n)
    (α : m ⟶ n) (z : ℤ) :
    chainMap (regular b) α (regularChainGenerator b s z) =
      regularChainGenerator b (restrictRegularSimplex b s α) z :=
  chainMap_regularGenerator b s α z

example (f : C(X, Y)) (b : X) (b' : Y) (hb : b' = f b)
    {n : SimplexCategory} (s : RegularSimplex b n) (z : ℤ) :
    regularPushforwardModuleMap f b b' hb n (regularChainGenerator b s z) =
      regularChainGenerator b' (mapRegularSimplex f b b' hb s) z :=
  regularPushforwardModuleMap_generator f b b' hb s z

example [PathConnectedSpace X] (f : C(X, Y)) (b x : X)
    (hf : Function.Bijective (HomotopyGroup.piMap 0 f (x := b) rfl))
    (q : Path.Homotopic.Quotient b x) :
    HomotopyGroup.pathClassMapEquiv f b x hf q = q.map f := rfl

example [PathConnectedSpace X] (f : C(X, Y)) (b : X) (b' : Y) (hb : b' = f b)
    (hf : Function.Bijective (HomotopyGroup.piMap 0 f (x := b) rfl)) :
    (regularCoefficientIso f b b' hb hf).hom = regularMapTo f b b' hb := rfl

example [PathConnectedSpace X] (f : C(X, Y)) (b : X) (b' : Y) (hb : b' = f b)
    (hf : Function.Bijective (HomotopyGroup.piMap 0 f (x := b) rfl)) :
    (regularCoefficientChainIso f b b' hb hf).hom =
      coefficientChainMap (regularMapTo f b b' hb) := rfl

example [PathConnectedSpace X] (f : C(X, Y)) (b : X) (b' : Y) (hb : b' = f b)
    (hf : Function.Bijective (HomotopyGroup.piMap 0 f (x := b) rfl)) :
    regularPushforwardChainMap f b b' hb =
      (regularCoefficientChainIso f b b' hb hf).hom ≫ pushforwardChainMap f (regular b') := rfl
