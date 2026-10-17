import PfaffianDescent.ProjectiveLinearChange
import PfaffianDescent.GeometricEvaluation
import PfaffianDescent.FrameIdealNormalization

namespace PfaffianDescent
open MvPolynomial Module
section
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

/-- Homogeneous restriction to the affine line represented by a vector over a
finite algebra. Its kernel is the vector's homogeneous projective ideal. -/
noncomputable def algebraLineHom (p : Vec A 4) :
    MvPolynomial (Fin 4) K →ₐ[K] MvPolynomial Unit A :=
  MvPolynomial.aeval (fun j => C (p j) * X ())

noncomputable def algebraVectorIdeal (p : Vec A 4) : Ideal (MvPolynomial (Fin 4) K) :=
  RingHom.ker (algebraLineHom (K := K) p).toRingHom

@[simp] lemma algebraLineHom_X (p : Vec A 4) (j : Fin 4) :
    algebraLineHom (K := K) p (X j) = C (p j) * X () := aeval_X _ _

@[simp] lemma algebraLineHom_C (p : Vec A 4) (a : K) :
    algebraLineHom p (C a) = C (algebraMap K A a) := by
  rw [algebraLineHom, aeval_C]
  rfl

end
section
variable {K A L : Type*} [Field K] [CommRing A] [Algebra K A]
    [Field L] [Algebra K L]

/-- Restriction to an algebra-valued line commutes with every geometric evaluation. -/
lemma algebraLineHom_geometric (p : Vec A 4) (f : A →ₐ[K] L) (g : MvPolynomial (Fin 4) K) :
    MvPolynomial.map f.toRingHom (algebraLineHom p g) =
      vectorLineHom (fun j => f (p j)) (MvPolynomial.map (algebraMap K L) g) := by
  have h : (MvPolynomial.map f.toRingHom).comp (algebraLineHom p).toRingHom =
      (vectorLineHom (fun j => f (p j))).toRingHom.comp (MvPolynomial.map (algebraMap K L)) := by
    ext a j
    · simp [algebraLineHom_C, vectorLineHom, AlgHom.commutes]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        algebraLineHom_X, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, vectorLineHom_X]
  exact DFunLike.congr_fun h g

variable [FiniteDimensional K A]

/-- The homogeneous ideal defined over the finite algebra equals the contraction
of the actual geometric projective-point ideal. -/
theorem algebraVectorIdeal_eq_geometric_contract (hdim : finrank K A = 5)
    (ev : Fin 5 → A →ₐ[K] L) (hev : Function.Injective ev) (p : Vec A 4) :
    algebraVectorIdeal (K := K) p =
      (fiveVectorIdeal (fun i j => ev i (p j))).comap (MvPolynomial.map (algebraMap K L)) := by
  ext g
  change algebraLineHom p g = 0 ↔
    MvPolynomial.map (algebraMap K L) g ∈ fiveVectorIdeal (fun i j => ev i (p j))
  rw [fiveVectorIdeal, Submodule.mem_iInf]
  change algebraLineHom p g = 0 ↔
    ∀ i, vectorLineHom (fun j => ev i (p j)) (MvPolynomial.map (algebraMap K L) g) = 0
  simp_rw [← algebraLineHom_geometric]
  constructor
  · intro h i
    rw [h, map_zero]
  · intro h
    apply MvPolynomial.ext
    intro d
    rw [coeff_zero]
    apply eq_zero_of_all_geometric_evaluations hdim ev hev
    intro i
    have hi := congrArg (coeff d) (h i)
    simpa only [coeff_map, coeff_zero, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using hi

end
end PfaffianDescent
