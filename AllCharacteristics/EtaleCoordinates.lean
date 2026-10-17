import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Étale coordinates from a basis of differentials

The Jacobi–Zariski exact sequence shows that a smooth algebra is formally
étale over a coefficient algebra when the base-changed differential map is
bijective. A differential basis identifies polynomial coordinates satisfying
this criterion.
-/

open scoped TensorProduct
open Algebra KaehlerDifferential
namespace AllCharacteristics
universe u v w i
variable (R : Type u) (A : Type v) (S : Type w)
variable [CommRing R] [CommRing A] [CommRing S]
variable [Algebra R A] [Algebra R S] [Algebra A S] [IsScalarTower R A S]

/-- A bijective differential base-change map and smoothness over the original
base imply formal étaleness over the intermediate algebra. -/
lemma formallyEtale_of_bijective_kaehlerBaseChange [Algebra.FormallySmooth R S]
    (h : Function.Bijective (KaehlerDifferential.mapBaseChange R A S)) :
    Algebra.FormallyEtale A S := by
  constructor
  · apply (subsingleton_iff_forall_eq (0 : KaehlerDifferential A S)).mpr
    intro x
    obtain ⟨y, rfl⟩ := KaehlerDifferential.map_surjective R A S x
    exact (KaehlerDifferential.exact_mapBaseChange_map R A S y).mpr (h.surjective y)
  · apply (subsingleton_iff_forall_eq (0 : Algebra.H1Cotangent A S)).mpr
    intro x
    have hx : Algebra.H1Cotangent.δ R A S x = 0 := by
      apply h.injective
      rw [map_zero]
      exact (Algebra.H1Cotangent.exact_δ_mapBaseChange R A S _).mpr ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ R A S x).mp hx
    rw [Subsingleton.elim y 0, map_zero]

variable {ι : Type i}

/-- Functions whose differentials form a basis give formally étale polynomial coordinates. -/
lemma formallyEtale_of_polynomial_differential_basis
    [Algebra (MvPolynomial ι R) S] [IsScalarTower R (MvPolynomial ι R) S]
    [Algebra.FormallySmooth R S]
    (b : Module.Basis ι S (KaehlerDifferential R S))
    (hb : ∀ i, b i = KaehlerDifferential.D R S
      (algebraMap (MvPolynomial ι R) S (MvPolynomial.X i))) :
    Algebra.FormallyEtale (MvPolynomial ι R) S := by
  let c : Module.Basis ι S (S ⊗[MvPolynomial ι R] KaehlerDifferential R (MvPolynomial ι R)) :=
    (KaehlerDifferential.mvPolynomialBasis R ι).baseChange S
  let e : (S ⊗[MvPolynomial ι R] KaehlerDifferential R (MvPolynomial ι R)) ≃ₗ[S]
      KaehlerDifferential R S := c.equiv b (Equiv.refl ι)
  have he : KaehlerDifferential.mapBaseChange R (MvPolynomial ι R) S = e.toLinearMap := by
    apply c.ext
    intro i
    change KaehlerDifferential.mapBaseChange R (MvPolynomial ι R) S (c i) = e (c i)
    rw [show e (c i) = b i from Module.Basis.equiv_apply c i b (Equiv.refl ι)]
    simpa only [c, Module.Basis.baseChange_apply, KaehlerDifferential.mvPolynomialBasis_apply,
      KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D, one_smul] using (hb i).symm
  apply formallyEtale_of_bijective_kaehlerBaseChange R (MvPolynomial ι R) S
  rw [he]
  exact e.bijective

end AllCharacteristics
