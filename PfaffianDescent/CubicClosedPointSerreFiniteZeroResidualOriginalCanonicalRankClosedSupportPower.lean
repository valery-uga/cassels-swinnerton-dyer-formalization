import AllCharacteristics.RelativeOrderedMaps
import PfaffianDescent.FiniteSchemeAlgebra
import Mathlib.RingTheory.Artinian.Module
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AllCharacteristics
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_finite_orderedSupportPower
    {S D : Scheme.{u}} (d : D ⟶ S) [IsFinite d] (n : ℕ) :
    IsFinite (orderedFamilyPowerOver d n).hom := by
  induction n with
  | zero => change IsFinite (𝟙 S); infer_instance
  | succ n ih =>
    letI := ih
    change IsFinite (pullback.fst d (orderedFamilyPowerOver d n).hom ≫ d)
    infer_instance

theorem cubicClosedPointSerreFiniteZeroResidual_finiteOverField_point_closed
    {K : Type u} [Field K] {D : Scheme.{u}} (d : D ⟶ Spec (.of K))
    [IsFinite d] (x : D) : IsClosed {x} := by
  letI : IsAffine D := isAffine_of_isAffineHom d
  letI := finiteSchemeCoefficientAlgebra d
  letI : Module.Finite K Γ(D, ⊤) := finiteSchemeCoefficient_finite d
  letI : IsArtinianRing Γ(D, ⊤) := IsArtinianRing.of_finite K Γ(D, ⊤)
  have hp : IsClosed {D.isoSpec.hom x} := by
    apply (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr
    exact (IsArtinianRing.isPrime_iff_isMaximal _).mp (D.isoSpec.hom x).isPrime
  have h := hp.preimage D.isoSpec.hom.continuous
  convert h using 1
  ext z
  simp only [Set.mem_singleton_iff, Set.mem_preimage]
  exact D.isoSpec.hom.isOpenEmbedding.injective.eq_iff.symm
end PfaffianDescent
