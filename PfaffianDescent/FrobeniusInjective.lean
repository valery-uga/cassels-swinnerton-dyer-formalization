import PfaffianDescent.AlgebraFrobenius
import Mathlib.Algebra.Module.Injective

namespace PfaffianDescent
open Module
section
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A] [FiniteDimensional K A]

/-- A finite commutative algebra with a nondegenerate multiplication functional
is injective as a module over itself. The proof verifies Baer's criterion. -/
theorem injective_of_frobenius (ell : Module.Dual K A) (hell : IsFrobeniusFunctional ell) :
    Module.Injective A A := by
  apply Module.Baer.injective
  intro I g
  let l : (I.restrictScalars K) →ₗ[K] K := ell.comp (g.restrictScalars K)
  obtain ⟨psi, hpsi⟩ := l.exists_extend
  obtain ⟨r, hr⟩ := frobeniusFunctional_surjective ell hell psi
  have hr' (a : A) : ell (r*a) = psi a := LinearMap.congr_fun hr a
  have hp (a : A) (ha : a ∈ I) : psi a = ell (g ⟨a, ha⟩) :=
    LinearMap.congr_fun hpsi ⟨a, ha⟩
  refine ⟨LinearMap.mulRight A r, ?_⟩
  intro x hx
  apply hell
  apply LinearMap.ext
  intro b
  change ell ((x*r)*b) = ell (g ⟨x, hx⟩ * b)
  have hb : b*x ∈ I := I.mul_mem_left b hx
  have hg : g ⟨b*x, hb⟩ = b * g ⟨x, hx⟩ := g.map_smul b ⟨x, hx⟩
  calc
    _ = ell (r * (b*x)) := by congr 1; ring
    _ = psi (b*x) := hr' _
    _ = ell (g ⟨b*x, hb⟩) := hp _ hb
    _ = ell (g ⟨x, hx⟩ * b) := by rw [hg, mul_comm b]

/-- Nondegeneracy of a multiplication functional is preserved by algebra isomorphism. -/
theorem frobenius_comp_equiv {B : Type*} [CommRing B] [Algebra K B]
    (e : B ≃ₐ[K] A) (ell : Module.Dual K A) (hell : IsFrobeniusFunctional ell) :
    IsFrobeniusFunctional (ell.comp e.toLinearMap) := by
  intro x y h
  apply e.injective
  apply hell
  apply LinearMap.ext
  intro a
  have he := LinearMap.congr_fun h (e.symm a)
  change ell (e (x * e.symm a)) = ell (e (y * e.symm a)) at he
  change ell (e x * a) = ell (e y * a)
  simpa only [map_mul, AlgEquiv.apply_symm_apply] using he

/-- The injectivity conclusion holds for any isomorphic algebra, including
an explicitly presented quotient ring. -/
theorem injective_of_frobenius_equiv {B : Type*} [CommRing B] [Algebra K B]
    (e : B ≃ₐ[K] A) (ell : Module.Dual K A) (hell : IsFrobeniusFunctional ell) :
    Module.Injective B B := by
  letI : FiniteDimensional K B := e.symm.toLinearEquiv.finiteDimensional
  exact injective_of_frobenius (ell.comp e.toLinearMap) (frobenius_comp_equiv e ell hell)

end
end PfaffianDescent
