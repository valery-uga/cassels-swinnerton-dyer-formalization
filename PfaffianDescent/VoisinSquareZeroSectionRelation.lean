import PfaffianDescent.VoisinSquareZeroTaylor
import Mathlib.RingTheory.Smooth.Basic

/-!
# The first-order relation supplied by a square-zero section

The first theorem expresses the difference of two algebra maps out of a
multivariate polynomial ring when their coordinate differences lie in a
square-zero ideal. The second applies it to a section of the first-order
thickening associated to a polynomial presentation.
-/

namespace PfaffianDescent

open MvPolynomial

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- The universal first-order relation between two polynomial algebra
maps whose coordinate differences are square-zero. -/
theorem mvPolynomial_algHom_difference_of_squareZero
    (u v : MvPolynomial (Fin 4) R →ₐ[R] A)
    (J : Ideal A) (hJ : J ^ 2 = ⊥)
    (hvars : ∀ i : Fin 4, v (X i) - u (X i) ∈ J)
    (p : MvPolynomial (Fin 4) R) :
    v p = u p +
      ∑ i : Fin 4, (v (X i) - u (X i)) * u (pderiv i p) := by
  let x : Fin 4 → A := fun i => u (X i)
  let y : Fin 4 → A := fun i => v (X i) - u (X i)
  have hy : ∀ i, y i ∈ J := hvars
  have hxy : ∀ i, x i + y i = v (X i) := by
    intro i
    simp [x, y]
  have hu : u = MvPolynomial.aeval x := by
    simpa [x, Function.comp_def] using (MvPolynomial.aeval_unique u)
  have hv : v = MvPolynomial.aeval (fun i => x i + y i) := by
    rw [MvPolynomial.aeval_unique v]
    congr 1
    funext i
    exact (hxy i).symm
  calc
    v p = p.eval₂ (algebraMap R A) (fun i => x i + y i) := by
      rw [hv]
      rfl
    _ = p.eval₂ (algebraMap R A) x +
        ∑ i : Fin 4, y i * (pderiv i p).eval₂ (algebraMap R A) x :=
      mvPolynomial_eval₂_add_of_squareZero (algebraMap R A) x y J hy hJ p
    _ = u p +
        ∑ i : Fin 4, (v (X i) - u (X i)) * u (pderiv i p) := by
      rw [hu]
      change (MvPolynomial.aeval x) p +
          ∑ i : Fin 4, y i * (MvPolynomial.aeval x) (pderiv i p) =
        (MvPolynomial.aeval x) p +
          ∑ i : Fin 4, (v (X i) - (MvPolynomial.aeval x) (X i)) *
            (MvPolynomial.aeval x) (pderiv i p)
      simp only [MvPolynomial.aeval_X]
      rfl

/-- A section of the square-zero thickening of a polynomial presentation
gives an explicit first-order Taylor relation for every polynomial. For a
polynomial in `ker f`, the left side is zero; the remaining displayed sum
is the relation from which a Jacobian Bézout identity must be extracted. -/
theorem mvPolynomial_kerSquareLift_section_relation
    (f : MvPolynomial (Fin 4) R →ₐ[R] A)
    (g : A →ₐ[R]
      MvPolynomial (Fin 4) R ⧸ RingHom.ker f.toRingHom ^ 2)
    (hg : f.kerSquareLift.comp g = AlgHom.id R A)
    (p : MvPolynomial (Fin 4) R) :
    g (f p) =
      Ideal.Quotient.mk (RingHom.ker f.toRingHom ^ 2) p +
        ∑ i : Fin 4,
          (g (f (X i)) -
            Ideal.Quotient.mk (RingHom.ker f.toRingHom ^ 2) (X i)) *
            Ideal.Quotient.mk (RingHom.ker f.toRingHom ^ 2)
              (pderiv i p) := by
  let I : Ideal (MvPolynomial (Fin 4) R) := RingHom.ker f.toRingHom
  let u : MvPolynomial (Fin 4) R →ₐ[R]
      MvPolynomial (Fin 4) R ⧸ I ^ 2 := Ideal.Quotient.mkₐ R (I ^ 2)
  let v : MvPolynomial (Fin 4) R →ₐ[R]
      MvPolynomial (Fin 4) R ⧸ I ^ 2 := g.comp f
  let J : Ideal (MvPolynomial (Fin 4) R ⧸ I ^ 2) :=
    RingHom.ker f.kerSquareLift.toRingHom
  have hJ : J ^ 2 = ⊥ := by
    change (RingHom.ker f.kerSquareLift.toRingHom) ^ 2 = ⊥
    rw [AlgHom.ker_kerSquareLift, Ideal.cotangentIdeal_square]
  have hsec (a : A) : f.kerSquareLift (g a) = a := by
    have h := DFunLike.congr_fun hg a
    simpa only [AlgHom.comp_apply, AlgHom.id_apply] using h
  have hu (i : Fin 4) : f.kerSquareLift (u (X i)) = f (X i) := by
    change f.kerSquareLift (Ideal.Quotient.mk (I ^ 2) (X i)) = f (X i)
    exact f.kerSquareLift_mk (X i)
  have hvars : ∀ i : Fin 4, v (X i) - u (X i) ∈ J := by
    intro i
    apply RingHom.mem_ker.mpr
    change f.kerSquareLift (g (f (X i)) - u (X i)) = 0
    rw [map_sub, hsec, hu]
    exact sub_self _
  have h := mvPolynomial_algHom_difference_of_squareZero u v J hJ hvars p
  simpa only [u, v, Ideal.Quotient.mkₐ_eq_mk, AlgHom.comp_apply] using h

/-- For a defining relation of the presented algebra, the section forces
the relation itself to be a linear combination of its partial derivatives
modulo the square of the presentation ideal. -/
theorem mvPolynomial_kerSquareLift_section_relation_of_mem
    (f : MvPolynomial (Fin 4) R →ₐ[R] A)
    (g : A →ₐ[R]
      MvPolynomial (Fin 4) R ⧸ RingHom.ker f.toRingHom ^ 2)
    (hg : f.kerSquareLift.comp g = AlgHom.id R A)
    (p : MvPolynomial (Fin 4) R)
    (hp : p ∈ RingHom.ker f.toRingHom) :
    Ideal.Quotient.mk (RingHom.ker f.toRingHom ^ 2) p +
        ∑ i : Fin 4,
          (g (f (X i)) -
            Ideal.Quotient.mk (RingHom.ker f.toRingHom ^ 2) (X i)) *
            Ideal.Quotient.mk (RingHom.ker f.toRingHom ^ 2)
              (pderiv i p) = 0 := by
  have hzero : f p = 0 := RingHom.mem_ker.mp hp
  simpa only [hzero, map_zero] using
    (mvPolynomial_kerSquareLift_section_relation f g hg p).symm

end PfaffianDescent
