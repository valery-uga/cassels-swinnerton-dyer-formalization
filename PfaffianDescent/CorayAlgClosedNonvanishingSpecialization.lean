import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Construct a nonvanishing field-valued specialization

This is the actual finite-type-domain specialization needed to attack prime
preservation under ARBITRARY, including transcendental, coefficient extension.
A maximal ideal avoiding the chosen element is constructed by Jacobsonity;
its residue field is internally identified with the original algebraically
closed field using Zariski's lemma. No point or nonvanishing certificate is
supplied. SOURCE ONLY / UNVERIFIED: root alone compiles and audits.
-/
noncomputable section
namespace PfaffianDescent.Coray
universe u v

/-- An actual finite-type domain over an algebraically closed field has an
actual field-valued algebra homomorphism where any chosen nonzero element
remains nonzero. The maximal ideal, finite residue extension and evaluation
are constructed internally; no localization/point certificate is supplied. -/
theorem finiteTypeDomain_exists_algHom_nonzero
    {Ω : Type u} {A : Type v} [Field Ω] [IsAlgClosed Ω]
    [CommRing A] [IsDomain A] [Algebra Ω A] [Algebra.FiniteType Ω A]
    (a : A) (ha : a ≠ 0) : ∃ φ : A →ₐ[Ω] Ω, φ a ≠ 0 := by
  classical
  letI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := Ω)
  have hJac : (⊥ : Ideal A).jacobson = ⊥ :=
    (isJacobsonRing_iff_prime_eq.mp (inferInstance : IsJacobsonRing A))
      (⊥ : Ideal A) inferInstance
  obtain ⟨m, ⟨_, hm⟩, ham⟩ :=
    (Ideal.eq_jacobson_iff_notMem (I := (⊥ : Ideal A))).mp hJac a
      (by simpa only [Ideal.mem_bot] using ha)
  letI : m.IsMaximal := hm
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  letI : Module.Finite Ω (A ⧸ m) :=
    finite_of_finite_type_of_isJacobsonRing Ω (A ⧸ m)
  let e : Ω ≃ₐ[Ω] (A ⧸ m) :=
    AlgEquiv.ofBijective (Algebra.ofId Ω (A ⧸ m))
      (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := Ω))
  let φ : A →ₐ[Ω] Ω := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ Ω m)
  refine ⟨φ, ?_⟩
  intro hzero
  apply ham
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply e.symm.injective
  simpa only [φ, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgEquiv.coe_toAlgHom, map_zero] using hzero

end PfaffianDescent.Coray
