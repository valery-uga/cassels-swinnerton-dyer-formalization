import PfaffianDescent.FiniteAlgebraGeometricPoints
import PfaffianDescent.FivePointAlgebraGorenstein
import PfaffianDescent.FivePointAlgebraResolution
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

namespace PfaffianDescent
open Module CategoryTheory
universe u
section
variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]

/-- No four distinct geometric points of the coordinate algebra are coplanar. -/
def AlgebraGeometricGeneralPosition (p : Fin 4 → A) : Prop :=
  ∀ ev : Fin 4 → A →ₐ[K] AlgebraicClosure K, Function.Injective ev →
    LinearIndependent (AlgebraicClosure K) (fun i j => ev i (p j))

lemma AlgebraGeometricGeneralPosition.five
    {p : Fin 4 → A} (hp : AlgebraGeometricGeneralPosition (K := K) p)
    (ev : Fin 5 → A →ₐ[K] AlgebraicClosure K) (hev : Function.Injective ev) :
    FivePointGeneralPosition (fun i j => ev i (p j)) := by
  intro e he
  exact hp (ev ∘ e) (hev.comp he)

variable [CharZero K] [Module.Finite K A] [IsReduced A]

/-- A reduced length-five coordinate algebra in geometric general position
gives a ground-field Pfaffian presentation; its geometric evaluations are constructed. -/
theorem reduced_five_algebra_polynomial_presentation
    (hdim : finrank K A = 5) (p : Fin 4 → A)
    (hp : AlgebraGeometricGeneralPosition (K := K) p)
    (f : MvPolynomial (Fin 4) K) (hf : f.IsHomogeneous 3)
    (hF : MvPolynomial.eval₂ (algebraMap K A) p f = 0) :
    ∃ P : Fin 4 → Mat K 6, (∀ i, IsAlternating (P i)) ∧
      (pfaffianCubic P).toMvPolynomial = f := by
  obtain ⟨ev, hev⟩ := reduced_finite_algebra_distinct_geometric_evaluations
    (L := AlgebraicClosure K) 5 hdim
  exact five_point_algebra_polynomial_presentation hdim ev hev p (hp.five ev hev) f hf hF

/-- The full minimal self-dual resolution for a reduced length-five algebra
requires only its actual geometric general position. -/
theorem reduced_five_algebra_free_resolution
    (hdim : finrank K A = 5) (p : Fin 4 → A)
    (hp : AlgebraGeometricGeneralPosition (K := K) p) :
    Nonempty (FiveQuadricResolution K (algebraVectorIdeal (K := K) p)) := by
  obtain ⟨ev, hev⟩ := reduced_finite_algebra_distinct_geometric_evaluations
    (L := AlgebraicClosure K) 5 hdim
  exact five_point_algebra_free_resolution hdim ev hev p (hp.five ev hev)

/-- Reducedness, length five, and geometric general position imply the
homogeneous coordinate ring is Gorenstein in the standard injective-dimension sense. -/
theorem reduced_five_algebra_homogeneous_gorenstein
    (hdim : finrank K A = 5) (p : Fin 4 → A)
    (hp : AlgebraGeometricGeneralPosition (K := K) p) :
    IsNoetherianRing (MvPolynomial (Fin 4) K ⧸ algebraVectorIdeal (K := K) p) ∧
      HasInjectiveDimensionLE
        (ModuleCat.of (MvPolynomial (Fin 4) K ⧸ algebraVectorIdeal (K := K) p)
          (MvPolynomial (Fin 4) K ⧸ algebraVectorIdeal (K := K) p)) 1 := by
  obtain ⟨ev, hev⟩ := reduced_finite_algebra_distinct_geometric_evaluations
    (L := AlgebraicClosure K) 5 hdim
  exact five_point_algebra_homogeneous_gorenstein hdim ev hev p (hp.five ev hev)

end
end PfaffianDescent
