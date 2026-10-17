import Mathlib.Algebra.MvPolynomial.Expand

/-!
# Normal form for the standard twisted cubic coordinate ring

The three quadratic relations reduce every polynomial to three binary
polynomial coefficients.  Their residue classes modulo degree three are
independent.
-/

/-! A normal form for the homogeneous coordinate ring of the twisted cubic. -/

namespace PfaffianDescent
namespace QuarticNet
open MvPolynomial
universe u

section Reduction
variable {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]

theorem twisted_cubic_normal_form (z : Fin 4 → A)
    (h1 : z 1 ^ 2 = z 0 * z 2)
    (h2 : z 1 * z 2 = z 0 * z 3)
    (h3 : z 2 ^ 2 = z 1 * z 3)
    (P : MvPolynomial (Fin 4) k) :
    ∃ a b c : MvPolynomial (Fin 2) k,
      MvPolynomial.aeval z P = MvPolynomial.aeval ![z 0,z 3] a +
        z 1 * MvPolynomial.aeval ![z 0,z 3] b +
        z 2 * MvPolynomial.aeval ![z 0,z 3] c := by
  induction P using MvPolynomial.induction_on with
  | C r => exact ⟨C r,0,0,by simp⟩
  | add P Q hP hQ =>
    obtain ⟨a,b,c,ha⟩ := hP
    obtain ⟨d,e,f,hd⟩ := hQ
    refine ⟨a+d,b+e,c+f,?_⟩
    simp only [map_add,ha,hd]
    ring
  | mul_X P i hP =>
    obtain ⟨a,b,c,ha⟩ := hP
    fin_cases i
    · refine ⟨X 0*a,X 0*b,X 0*c,?_⟩
      simp [ha]
      ring
    · refine ⟨X 0*X 1*c,a,X 0*b,?_⟩
      simp [ha]
      linear_combination MvPolynomial.aeval ![z 0,z 3] b*h1 +
        MvPolynomial.aeval ![z 0,z 3] c*h2
    · refine ⟨X 0*X 1*b,X 1*c,a,?_⟩
      simp [ha]
      linear_combination MvPolynomial.aeval ![z 0,z 3] b*h2 +
        MvPolynomial.aeval ![z 0,z 3] c*h3
    · refine ⟨X 1*a,X 1*b,X 1*c,?_⟩
      simp [ha]
      ring

end Reduction

noncomputable def cubicResidueExponent : Fin 3 → (Fin 2 →₀ ℕ) :=
  ![0,Finsupp.single 0 2+Finsupp.single 1 1,Finsupp.single 0 1+Finsupp.single 1 2]

noncomputable def cubicSlotExponent (r : Fin 3) (d : Fin 2 →₀ ℕ) : Fin 2 →₀ ℕ :=
  3 • d + cubicResidueExponent r

theorem cubicSlotExponent_joint_injective :
    Function.Injective (fun p : Fin 3 × (Fin 2 →₀ ℕ) => cubicSlotExponent p.1 p.2) := by
  rintro ⟨r,d⟩ ⟨s,e⟩ h
  have ht := congrArg (fun f : Fin 2 →₀ ℕ => f 1) h
  have hrs : r=s := by
    fin_cases r <;> fin_cases s <;>
      simp +decide [cubicSlotExponent,cubicResidueExponent,Finsupp.single_apply,
        nsmul_eq_mul] at ht ⊢ <;> omega
  subst s
  apply congrArg (Prod.mk r)
  ext i
  have hi := congrArg (fun f : Fin 2 →₀ ℕ => f i) h
  simp only [cubicSlotExponent,Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul] at hi
  omega

noncomputable def cubicSlotEmbedding (r : Fin 3) : (Fin 2 →₀ ℕ) ↪ (Fin 2 →₀ ℕ) where
  toFun := cubicSlotExponent r
  inj' d e h := (Prod.mk.inj (@cubicSlotExponent_joint_injective (r,d) (r,e) h)).2

noncomputable def cubicSlot {k : Type u} [CommRing k] (r : Fin 3)
    (P : MvPolynomial (Fin 2) k) : MvPolynomial (Fin 2) k :=
  AddMonoidAlgebra.ofCoeff (Finsupp.embDomain (cubicSlotEmbedding r)
    (AddMonoidAlgebra.coeff P))

theorem cubicSlot_coeff_self {k : Type u} [CommRing k] (r : Fin 3)
    (P : MvPolynomial (Fin 2) k) (d : Fin 2 →₀ ℕ) :
    coeff (cubicSlotExponent r d) (cubicSlot r P) = coeff d P := by
  change (Finsupp.embDomain (cubicSlotEmbedding r) (AddMonoidAlgebra.coeff P))
      (cubicSlotExponent r d) = coeff d P
  exact Finsupp.embDomain_apply_self _ _ _

theorem cubicSlot_coeff_other {k : Type u} [CommRing k] (r s : Fin 3) (hrs : r ≠ s)
    (P : MvPolynomial (Fin 2) k) (d : Fin 2 →₀ ℕ) :
    coeff (cubicSlotExponent r d) (cubicSlot s P) = 0 := by
  apply Finsupp.embDomain_of_notMem_range
  rintro ⟨e,he⟩
  have h := @cubicSlotExponent_joint_injective (s,e) (r,d) he
  exact hrs (congrArg Prod.fst h).symm

theorem cubicSlot_add {k : Type u} [CommRing k] (r : Fin 3)
    (P Q : MvPolynomial (Fin 2) k) :
    cubicSlot r (P + Q) = cubicSlot r P + cubicSlot r Q := by
  ext d
  change (Finsupp.embDomain (cubicSlotEmbedding r) (AddMonoidAlgebra.coeff (P + Q))) d =
    (Finsupp.embDomain (cubicSlotEmbedding r) (AddMonoidAlgebra.coeff P)) d +
      (Finsupp.embDomain (cubicSlotEmbedding r) (AddMonoidAlgebra.coeff Q)) d
  rw [AddMonoidAlgebra.coeff_add, Finsupp.embDomain_add]
  rfl

theorem cubicSlots_independent {k : Type u} [CommRing k]
    (a b c : MvPolynomial (Fin 2) k)
    (h : cubicSlot 0 a+cubicSlot 1 b+cubicSlot 2 c=0) : a=0 ∧ b=0 ∧ c=0 := by
  constructor
  · ext d
    have hd := congrArg (coeff (cubicSlotExponent 0 d)) h
    simpa only [coeff_add,cubicSlot_coeff_self,cubicSlot_coeff_other 0 1 (by decide),
      cubicSlot_coeff_other 0 2 (by decide),add_zero,coeff_zero] using hd
  constructor
  · ext d
    have hd := congrArg (coeff (cubicSlotExponent 1 d)) h
    simpa only [coeff_add,cubicSlot_coeff_self,cubicSlot_coeff_other 1 0 (by decide),
      cubicSlot_coeff_other 1 2 (by decide),add_zero,zero_add,coeff_zero] using hd
  · ext d
    have hd := congrArg (coeff (cubicSlotExponent 2 d)) h
    simpa only [coeff_add,cubicSlot_coeff_self,cubicSlot_coeff_other 2 0 (by decide),
      cubicSlot_coeff_other 2 1 (by decide),add_zero,zero_add,coeff_zero] using hd

section CubicExpansion
variable {k : Type u} [CommRing k]

noncomputable def cubicExpansion : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 2) k :=
  MvPolynomial.aeval ![X 0^3,X 1^3]

theorem cubicExpansion_monomial (d : Fin 2 →₀ ℕ) (a : k) :
    cubicExpansion (monomial d a) = monomial (3 • d) a := by
  simp [cubicExpansion,aeval_monomial,monomial_eq,Finsupp.prod_fintype,
    Fin.prod_univ_two,pow_mul,nsmul_eq_mul]

theorem cubicSlot_eq_expansion (r : Fin 3) (P : MvPolynomial (Fin 2) k) :
    cubicSlot r P = monomial (cubicResidueExponent r) 1*cubicExpansion P := by
  induction P using MvPolynomial.induction_on' with
  | monomial d a =>
    have hcoeff : AddMonoidAlgebra.coeff (monomial d a : MvPolynomial (Fin 2) k) =
        Finsupp.single d a := by
      ext e
      change coeff e (monomial d a : MvPolynomial (Fin 2) k) = _
      rw [coeff_monomial, Finsupp.single_apply]
    rw [cubicSlot, hcoeff]
    rw [Finsupp.embDomain_single, AddMonoidAlgebra.ofCoeff_single,
      cubicExpansion_monomial, monomial_mul]
    change monomial (3 • d+cubicResidueExponent r) a =
      monomial (cubicResidueExponent r+3 • d) (1*a)
    rw [one_mul,add_comm]
  | add P Q hP hQ =>
    rw [cubicSlot_add, map_add, mul_add, hP, hQ]

theorem twisted_cubic_normal_form_unique (a b c : MvPolynomial (Fin 2) k)
    (h : cubicExpansion a + X 0^2*X 1*cubicExpansion b +
      X 0*X 1^2*cubicExpansion c = 0) : a=0 ∧ b=0 ∧ c=0 := by
  apply cubicSlots_independent
  simpa [cubicSlot_eq_expansion,cubicResidueExponent,monomial_eq,
    Finsupp.prod_fintype,Fin.prod_univ_two,Finsupp.single_apply] using h

end CubicExpansion

end QuarticNet
end PfaffianDescent
