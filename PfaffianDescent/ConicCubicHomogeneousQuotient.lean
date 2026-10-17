import PfaffianDescent.ConicCubicGradedComplex
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

namespace PfaffianDescent
open MvPolynomial
section
variable {K : Type*} [Field K]

noncomputable def conicCubicIdeal (q f : MvPolynomial (Fin 3) K) : Ideal (MvPolynomial (Fin 3) K) :=
  Ideal.span ({q, f} : Set (MvPolynomial (Fin 3) K))

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The intersection ideal is a homogeneous ideal. -/
lemma conicCubicIdeal_homogeneous (q f : MvPolynomial (Fin 3) K)
    (hq : q.IsHomogeneous 2) (hf : f.IsHomogeneous 3) :
    (conicCubicIdeal q f).IsHomogeneous (homogeneousSubmodule (Fin 3) K) := by
  apply Ideal.homogeneous_span
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · exact ⟨2, hq⟩
  · exact ⟨3, hf⟩

noncomputable def conicCubicHomogeneousIdeal (q f : MvPolynomial (Fin 3) K)
    (hq : q.IsHomogeneous 2) (hf : f.IsHomogeneous 3) :
    HomogeneousIdeal (homogeneousSubmodule (Fin 3) K) :=
  ⟨conicCubicIdeal q f, conicCubicIdeal_homogeneous q f hq hf⟩

/-- The actual degree-d component inside the homogeneous coordinate quotient. -/
noncomputable def conicCubicComponent (q f : MvPolynomial (Fin 3) K) (d : ℕ) :
    Submodule K (MvPolynomial (Fin 3) K ⧸ conicCubicIdeal q f) :=
  (PlaneHomogeneous K d).map (Ideal.Quotient.mkₐ K (conicCubicIdeal q f)).toLinearMap

noncomputable def conicCubicProjection (q f : MvPolynomial (Fin 3) K) (d : ℕ) :
    PlaneHomogeneous K d →ₗ[K] (MvPolynomial (Fin 3) K ⧸ conicCubicIdeal q f) :=
  (Ideal.Quotient.mkₐ K (conicCubicIdeal q f)).toLinearMap.comp (PlaneHomogeneous K d).subtype

lemma conicCubicProjection_range (q f : MvPolynomial (Fin 3) K) (d : ℕ) :
    LinearMap.range (conicCubicProjection q f d) = conicCubicComponent q f d := by
  rw [conicCubicProjection, LinearMap.range_comp, Submodule.range_subtype]
  rfl

/-- The graded last Koszul map has exactly the kernel of the actual quotient projection. -/
theorem conicCubicProjection_exact (q f : MvPolynomial (Fin 3) K)
    (hq : q.IsHomogeneous 2) (hf : f.IsHomogeneous 3) (d : ℕ) :
    LinearMap.range (conicCubicGradedLast q f hq hf d) =
      LinearMap.ker (conicCubicProjection q f (d+5)) := by
  apply le_antisymm
  · rintro v ⟨a, rfl⟩
    change Ideal.Quotient.mk (conicCubicIdeal q f) (q*a.1.val + f*a.2.val) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change q*a.1.val + f*a.2.val ∈ Ideal.span ({q,f} : Set (MvPolynomial (Fin 3) K))
    rw [← twoGeneratorLast_range]
    exact ⟨(a.1.val,a.2.val), rfl⟩
  · intro v hv
    change Ideal.Quotient.mk (conicCubicIdeal q f) v.val = 0 at hv
    have hvmem := Ideal.Quotient.eq_zero_iff_mem.mp hv
    change v.val ∈ Ideal.span ({q,f} : Set (MvPolynomial (Fin 3) K)) at hvmem
    rw [← twoGeneratorLast_range] at hvmem
    obtain ⟨⟨a,b⟩, hab⟩ := hvmem
    change q*a + f*b = v.val at hab
    refine ⟨(⟨homogeneousComponent (d+3) a, homogeneousComponent_isHomogeneous _ _⟩,
      ⟨homogeneousComponent (d+2) b, homogeneousComponent_isHomogeneous _ _⟩), ?_⟩
    apply Subtype.ext
    change q*homogeneousComponent (d+3) a + f*homogeneousComponent (d+2) b = v.val
    have hqa : homogeneousComponent (d+5) (q*a) = q*homogeneousComponent (d+3) a := by
      rw [show d+5 = 2+(d+3) from by omega]
      exact homogeneousComponent_mul_left (q := a) hq (d+3)
    have hfb : homogeneousComponent (d+5) (f*b) = f*homogeneousComponent (d+2) b := by
      rw [show d+5 = 3+(d+2) from by omega]
      exact homogeneousComponent_mul_left (q := b) hf (d+2)
    rw [← hqa, ← hfb, ← map_add, hab, homogeneousComponent_eq_self v.property]

end
end PfaffianDescent
