import AllCharacteristics.FlatPushoutKernelIdeal
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Scheme-theoretic image and flat base change on affine charts

The actual global-section pushout identifies the base-changed kernel ideal.
Comparing with the closed subscheme cut out by the original kernel yields
the scheme-theoretic image equality, expressed using actual ideal sheaves.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u

/-- The actual global-section kernels in a flat affine Cartesian square
are related by extension of ideals. -/
lemma map_kernel_appTop_of_affine_flat_pullback
    {P X Y Y' : Scheme.{u}} [IsAffine P] [IsAffine X] [IsAffine Y] [IsAffine Y']
    {a : P ⟶ X} {b : P ⟶ Y'} {i : X ⟶ Y} {g : Y' ⟶ Y}
    (h : IsPullback a b i g) [Flat g] :
    (RingHom.ker i.appTop.hom).map g.appTop.hom = RingHom.ker b.appTop.hom := by
  let := g.appTop.hom.toAlgebra
  let := i.appTop.hom.toAlgebra
  let := b.appTop.hom.toAlgebra
  let := a.appTop.hom.toAlgebra
  let := (b ≫ g).appTop.hom.toAlgebra
  have : IsScalarTower Γ(Y, ⊤) Γ(Y', ⊤) Γ(P, ⊤) :=
    IsScalarTower.of_algebraMap_eq' (by
      change (b ≫ g).appTop.hom = b.appTop.hom.comp g.appTop.hom
      rw [Scheme.Hom.comp_appTop]
      rfl)
  have : IsScalarTower Γ(Y, ⊤) Γ(X, ⊤) Γ(P, ⊤) :=
    IsScalarTower.of_algebraMap_eq' (by
      change (b ≫ g).appTop.hom = a.appTop.hom.comp i.appTop.hom
      rw [← h.w, Scheme.Hom.comp_appTop]
      rfl)
  have : Module.Flat Γ(Y, ⊤) Γ(Y', ⊤) :=
    RingHom.flat_algebraMap_iff.mp g.flat_appTop
  have : Algebra.IsPushout Γ(Y, ⊤) Γ(Y', ⊤) Γ(X, ⊤) Γ(P, ⊤) :=
    CommRingCat.isPushout_iff_isPushout.mp (isPushout_appTop_of_isPullback h).flip
  exact flatPushout_map_kernel Γ(Y, ⊤) Γ(Y', ⊤) Γ(X, ⊤) Γ(P, ⊤)

/-- Scheme-theoretic image commutes with flat base change in an actual
Cartesian square of affine schemes. -/
lemma kernel_of_affine_flat_pullback
    {P X Y Y' : Scheme.{u}} [IsAffine P] [IsAffine X] [IsAffine Y] [IsAffine Y']
    {a : P ⟶ X} {b : P ⟶ Y'} {i : X ⟶ Y} {g : Y' ⟶ Y}
    (h : IsPullback a b i g) [Flat g] : b.ker = i.ker.comap g := by
  let j := i.ker.subschemeι
  have : IsAffine i.ker.subscheme := isAffine_of_isAffineHom i.ker.subschemeι
  have hj : RingHom.ker j.appTop.hom = RingHom.ker i.appTop.hom := by
    have he := congrArg (fun I : Y.IdealSheafData => I.ideal ⟨⊤, isAffineOpen_top Y⟩)
      i.ker.ker_subschemeι
    simpa [Scheme.ker_of_isAffine] using he
  have h₁ := map_kernel_appTop_of_affine_flat_pullback h
  have h₂ := map_kernel_appTop_of_affine_flat_pullback (IsPullback.of_hasPullback g j).flip
  rw [hj] at h₂
  change b.ker = (pullback.fst g j).ker
  rw [Scheme.ker_of_isAffine, Scheme.ker_of_isAffine]
  exact congrArg Scheme.IdealSheafData.ofIdealTop (h₁.symm.trans h₂)

end AllCharacteristics
