import PfaffianDescent.QuarticTwistedCubicNormalForm

/-! The defining ideal of the standard twisted cubic is the kernel of its
polynomial parametrization. This is an equality of ideals, not just of
geometric point sets. -/

namespace PfaffianDescent
namespace QuarticNet
open MvPolynomial
universe u
variable (k : Type u) [CommRing k]

noncomputable def standardTwistedCubicGenerators : Fin 3 → MvPolynomial (Fin 4) k :=
  ![X 1^2-X 0*X 2,X 1*X 2-X 0*X 3,X 2^2-X 1*X 3]

noncomputable def standardTwistedCubicIdeal : Ideal (MvPolynomial (Fin 4) k) :=
  Ideal.span (Set.range (standardTwistedCubicGenerators k))

/-- The three standard twisted-cubic generators are homogeneous quadrics. -/
theorem standardTwistedCubicGenerators_homogeneous (i : Fin 3) :
    (standardTwistedCubicGenerators k i).IsHomogeneous 2 := by
  have h (i j : Fin 4) : (X (R := k) i * X j).IsHomogeneous 2 :=
    (isHomogeneous_X k i).mul (isHomogeneous_X k j)
  fin_cases i
  · exact (isHomogeneous_X_pow 1 2).sub (h 0 2)
  · exact (h 1 2).sub (h 0 3)
  · exact (isHomogeneous_X_pow 2 2).sub (h 1 3)

noncomputable def standardTwistedCubicParam :
    MvPolynomial (Fin 4) k →ₐ[k] MvPolynomial (Fin 2) k :=
  MvPolynomial.aeval ![X 0^3,X 0^2*X 1,X 0*X 1^2,X 1^3]

theorem standardTwistedCubicIdeal_le_ker :
    standardTwistedCubicIdeal k ≤ RingHom.ker (standardTwistedCubicParam k).toRingHom := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i,rfl⟩
  change standardTwistedCubicParam k (standardTwistedCubicGenerators k i) = 0
  fin_cases i <;> simp [standardTwistedCubicParam,standardTwistedCubicGenerators] <;> ring

noncomputable def standardTwistedCubicQuotientParam :
    (MvPolynomial (Fin 4) k ⧸ standardTwistedCubicIdeal k) →ₐ[k] MvPolynomial (Fin 2) k :=
  Ideal.Quotient.liftₐ _ (standardTwistedCubicParam k) (standardTwistedCubicIdeal_le_ker k)

theorem standardTwistedCubicQuotientParam_mk (P : MvPolynomial (Fin 4) k) :
    standardTwistedCubicQuotientParam k (Ideal.Quotient.mk (standardTwistedCubicIdeal k) P) =
      standardTwistedCubicParam k P := rfl

theorem standardTwistedCubicIdeal_eq_ker :
    standardTwistedCubicIdeal k = RingHom.ker (standardTwistedCubicParam k).toRingHom := by
  apply le_antisymm (standardTwistedCubicIdeal_le_ker k)
  intro P hP
  let q := Ideal.Quotient.mkₐ k (standardTwistedCubicIdeal k)
  let z : Fin 4 → (MvPolynomial (Fin 4) k ⧸ standardTwistedCubicIdeal k) := fun i => q (X i)
  have hrel (i : Fin 3) : q (standardTwistedCubicGenerators k i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))
  have h1 : z 1^2=z 0*z 2 := by
    have h := hrel 0
    simpa [standardTwistedCubicGenerators,map_sub,sub_eq_zero,z] using h
  have h2 : z 1*z 2=z 0*z 3 := by
    have h := hrel 1
    simpa [standardTwistedCubicGenerators,map_sub,sub_eq_zero,z] using h
  have h3 : z 2^2=z 1*z 3 := by
    have h := hrel 2
    simpa [standardTwistedCubicGenerators,map_sub,sub_eq_zero,z] using h
  obtain ⟨a,b,c,hnormal⟩ := twisted_cubic_normal_form z h1 h2 h3 P
  have hq : MvPolynomial.aeval z = q := (MvPolynomial.aeval_unique q).symm
  rw [hq] at hnormal
  have hv (i : Fin 4) : standardTwistedCubicQuotientParam k (z i) =
      ![X 0^3,X 0^2*X 1,X 0*X 1^2,X 1^3] i := by
    change standardTwistedCubicParam k (X i) = _
    simp [standardTwistedCubicParam]
  have he : (standardTwistedCubicQuotientParam k).comp (MvPolynomial.aeval ![z 0,z 3]) =
      cubicExpansion := by
    ext i
    fin_cases i <;> simp [cubicExpansion,hv]
  have he' (Q : MvPolynomial (Fin 2) k) :
      standardTwistedCubicQuotientParam k (MvPolynomial.aeval ![z 0,z 3] Q) =
        cubicExpansion Q := AlgHom.congr_fun he Q
  have heval := congrArg (standardTwistedCubicQuotientParam k) hnormal
  have hpzero : standardTwistedCubicParam k P = 0 := hP
  change standardTwistedCubicParam k P = _ at heval
  rw [hpzero] at heval
  simp only [map_add,map_mul,he',hv,Matrix.cons_val_one,Matrix.cons_val_zero,
    Matrix.cons_val_two] at heval
  obtain ⟨ha,hb,hc⟩ := twisted_cubic_normal_form_unique a b c heval.symm
  rw [ha,hb,hc] at hnormal
  have hzero : q P=0 := by simpa using hnormal
  exact Ideal.Quotient.eq_zero_iff_mem.mp hzero

theorem standardTwistedCubicIdeal_isPrime [IsDomain k] : (standardTwistedCubicIdeal k).IsPrime := by
  rw [standardTwistedCubicIdeal_eq_ker]
  exact RingHom.ker_isPrime (standardTwistedCubicParam k).toRingHom

noncomputable def standardTwistedCubicCoordinateRingEquiv :
    (MvPolynomial (Fin 4) k ⧸ standardTwistedCubicIdeal k) ≃ₐ[k] (standardTwistedCubicParam k).range :=
  (Ideal.quotientEquivAlgOfEq k (standardTwistedCubicIdeal_eq_ker k)).trans
    (Ideal.quotientKerEquivRange (standardTwistedCubicParam k))

end QuarticNet
end PfaffianDescent
