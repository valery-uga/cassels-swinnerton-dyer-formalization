import AllCharacteristics.SquareZeroActualBasisLifting
import AllCharacteristics.RegularPairLiftedIdealIntersection
import AllCharacteristics.EmbeddedIdealNilpotentReduction
import Mathlib.RingTheory.LocalRing.Module

/-! Actual finite-flat lifting of an already prescribed two-generator
embedded deformation across a square-zero test-algebra extension.
The original downstream algebra, ideal, scalar action, and basis are retained.
-/

open Module LinearMap TensorProduct
open scoped nonZeroDivisors
namespace AllCharacteristics
universe u v w t

/-- Whole coefficient reduction, with the original downstairs scalar action.
The quotient by the coefficient kernel occurs only inside the construction. -/
noncomputable def actualCoefficientReductionEquiv166
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (hRS : Function.Surjective (algebraMap R S))
    {M : Type w} {N : Type t} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module S N] [IsScalarTower R S N]
    (q : M →ₗ[R] N) (hq : Function.Surjective q)
    (hker : q.ker = RingHom.ker (algebraMap R S) • (⊤ : Submodule R M)) :
    (S ⊗[R] M) ≃ₗ[S] N := by
  let I := RingHom.ker (algebraMap R S)
  let e := (Ideal.quotientKerAlgEquivOfSurjective
    (f := Algebra.ofId R S) hRS).toLinearEquiv
  let eCoef := e.rTensor M
  let eQuot : ((R ⧸ I) ⊗[R] M) ≃ₗ[R] N :=
    (TensorProduct.quotTensorEquivQuotSMul M I).trans
      ((Submodule.quotEquivOfEq _ _ hker.symm).trans
        (q.quotKerEquivOfSurjective hq))
  exact (eCoef.symm.trans eQuot).extendScalarsOfSurjective hRS

/-- This equivalence is the actual quotient reduction on every element. -/
theorem actualCoefficientReductionEquiv166_one_tmul
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (hRS : Function.Surjective (algebraMap R S))
    {M : Type w} {N : Type t} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module S N] [IsScalarTower R S N]
    (q : M →ₗ[R] N) (hq : Function.Surjective q)
    (hker : q.ker = RingHom.ker (algebraMap R S) • (⊤ : Submodule R M))
    (m : M) :
    actualCoefficientReductionEquiv166 hRS q hq hker ((1 : S) ⊗ₜ[R] m) = q m := by
  let I := RingHom.ker (algebraMap R S)
  let e : (R ⧸ I) ≃ₐ[R] S :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R S) hRS
  have heone : e.toLinearEquiv.symm (1 : S) = (1 : R ⧸ I) := by
    change e.symm (1 : S) = (1 : R ⧸ I)
    exact map_one e.symm
  change (q.quotKerEquivOfSurjective hq)
    (Submodule.quotEquivOfEq (I • (⊤ : Submodule R M)) q.ker hker.symm
      (TensorProduct.quotTensorEquivQuotSMul M I
        (e.toLinearEquiv.symm.rTensor M ((1 : S) ⊗ₜ[R] m)))) = q m
  rw [LinearEquiv.rTensor_tmul, heone,
    TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- Lift the entire prescribed finite free embedded quotient.  The tensor
injection is derived from ambient flatness and the explicit regular pair;
neither an upstairs flatness premise nor an obstruction certificate is used. -/
theorem liftedRegularPair_prescribedFiniteFreeFlat166
    {R : Type u} {S : Type v} {A' : Type w} {A : Type t}
    [CommRing R] [Nontrivial R] [CommRing S] [CommRing A'] [CommRing A]
    [Algebra R S] [Algebra R A'] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] [Module.Flat R A']
    (hRS : Function.Surjective (algebraMap R S))
    (hI : (RingHom.ker (algebraMap R S)) ^ 2 = ⊥)
    (π : A' →ₐ[R] A) (hπ : Function.Surjective π)
    (hK : RingHom.ker π.toRingHom =
      (RingHom.ker (algebraMap R S)).map (algebraMap R A'))
    (f' g' : A') (J : Ideal A)
    (hJ : J = (Ideal.span ({f', g'} : Set A')).map π.toRingHom)
    (hf : π f' ∈ A⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {π f'}) (π g') ∈
      (A ⧸ Ideal.span {π f'})⁰)
    (d : ℕ) (b : Basis (Fin d) S (A ⧸ J)) :
    ∃ b' : Basis (Fin d) R (A' ⧸ Ideal.span ({f', g'} : Set A')),
      Module.Finite R (A' ⧸ Ideal.span ({f', g'} : Set A')) ∧
      Module.Free R (A' ⧸ Ideal.span ({f', g'} : Set A')) ∧
      Module.Flat R (A' ⧸ Ideal.span ({f', g'} : Set A')) ∧
      Module.finrank R (A' ⧸ Ideal.span ({f', g'} : Set A')) = d ∧
      ∀ i, (Ideal.quotientEquivAlgOfEq S hJ.symm)
        (embeddedIdealReduction165 π (Ideal.span ({f', g'} : Set A')) (b' i)) = b i := by
  let I := RingHom.ker (algebraMap R S)
  let J' := Ideal.span ({f', g'} : Set A')
  let Q' := A' ⧸ J'
  let Q := A ⧸ J'.map π.toRingHom
  let ρ := embeddedIdealReduction165 π J'
  have hρ : Function.Surjective ρ := embeddedIdealReduction165_surjective π hπ J'
  have hρK : RingHom.ker ρ.toRingHom = I.map (algebraMap R Q') := by
    rw [embeddedIdealReduction165_ker π hπ J', hK, Ideal.map_map]
    rfl
  have hρker : ρ.toLinearMap.ker = I • (⊤ : Submodule R Q') := by
    ext x
    change x ∈ RingHom.ker ρ.toRingHom ↔ x ∈ I • (⊤ : Submodule R Q')
    rw [hρK, Ideal.smul_top_eq_map]
    rfl
  let e : (S ⊗[R] Q') ≃ₗ[S] Q :=
    actualCoefficientReductionEquiv166 hRS ρ.toLinearMap hρ hρker
  let bQ : Basis (Fin d) S Q := b.map (Ideal.quotientEquivAlgOfEq S hJ).toLinearEquiv
  let bTensor : Basis (Fin d) S (S ⊗[R] Q') := bQ.map e.symm
  have hinter : I.map (algebraMap R A') ⊓ J' = I.map (algebraMap R A') * J' := by
    rw [← hK]
    exact liftedRegularPair_kernel_inf_eq_mul165 π.toRingHom hπ f' g' hf hg
  have hmu : Function.Injective (idealTensorMultiplication166 I Q') :=
    quotient_idealTensorMultiplication166_injective I J' hinter
  obtain ⟨b', hfinite, hfree, hflat, hrank, hb'⟩ :=
    finite_free_flat_sameRank_of_square_zero_actualReduction166 hRS hI d bTensor hmu
  refine ⟨b', hfinite, hfree, hflat, hrank, ?_⟩
  intro i
  have hρb : ρ (b' i) = bQ i := by
    change ρ.toLinearMap (b' i) = bQ i
    rw [← actualCoefficientReductionEquiv166_one_tmul hRS ρ.toLinearMap hρ hρker,
      hb' i]
    change e (bTensor i) = bQ i
    simp [bTensor]
  change (Ideal.quotientEquivAlgOfEq S hJ.symm) (ρ (b' i)) = b i
  rw [hρb]
  change (Ideal.quotientEquivAlgOfEq S hJ.symm)
    ((Ideal.quotientEquivAlgOfEq S hJ) (b i)) = b i
  rw [← Ideal.quotientEquivAlgOfEq_symm]
  exact (Ideal.quotientEquivAlgOfEq S hJ).symm_apply_apply (b i)

/-- Over the actual local downstairs test algebra, finite flatness supplies
the downstairs basis internally.  The whole prescribed ideal is retained. -/
theorem liftedRegularPair_prescribedFiniteFlat_local166
    {R : Type u} {S : Type v} {A' : Type w} {A : Type t}
    [CommRing R] [CommRing S] [IsLocalRing S]
    [CommRing A'] [CommRing A]
    [Algebra R S] [Algebra R A'] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] [Module.Flat R A']
    (hRS : Function.Surjective (algebraMap R S))
    (hI : (RingHom.ker (algebraMap R S)) ^ 2 = ⊥)
    (π : A' →ₐ[R] A) (hπ : Function.Surjective π)
    (hK : RingHom.ker π.toRingHom =
      (RingHom.ker (algebraMap R S)).map (algebraMap R A'))
    (f' g' : A') (J : Ideal A)
    (hJ : J = (Ideal.span ({f', g'} : Set A')).map π.toRingHom)
    (hf : π f' ∈ A⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {π f'}) (π g') ∈
      (A ⧸ Ideal.span {π f'})⁰)
    [Module.Finite S (A ⧸ J)] [Module.Flat S (A ⧸ J)] :
    Module.Finite R (A' ⧸ Ideal.span ({f', g'} : Set A')) ∧
      Module.Free R (A' ⧸ Ideal.span ({f', g'} : Set A')) ∧
      Module.Flat R (A' ⧸ Ideal.span ({f', g'} : Set A')) ∧
      Module.finrank R (A' ⧸ Ideal.span ({f', g'} : Set A')) = Module.finrank S (A ⧸ J) := by
  letI : Nontrivial R := (algebraMap R S).domain_nontrivial
  letI : Module.Free S (A ⧸ J) := Module.free_of_flat_of_isLocalRing
  obtain ⟨b', hfinite, hfree, hflat, hrank, hb'⟩ :=
    liftedRegularPair_prescribedFiniteFreeFlat166 hRS hI π hπ hK f' g' J hJ hf hg
      (Module.finrank S (A ⧸ J)) (Module.finBasis S (A ⧸ J))
  exact ⟨hfinite, hfree, hflat, hrank⟩

/-- Construct the lifted generators of the already prescribed downstairs
ideal, and prove that their entire quotient is finite flat of the same rank.
Only the explicit regular-pair data downstairs is required. -/
theorem exists_prescribed_regularPair_finiteFlat_lift166
    {R : Type u} {S : Type v} {A' : Type w} {A : Type t}
    [CommRing R] [CommRing S] [IsLocalRing S]
    [CommRing A'] [CommRing A]
    [Algebra R S] [Algebra R A'] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] [Module.Flat R A']
    (hRS : Function.Surjective (algebraMap R S))
    (hI : (RingHom.ker (algebraMap R S)) ^ 2 = ⊥)
    (π : A' →ₐ[R] A) (hπ : Function.Surjective π)
    (hK : RingHom.ker π.toRingHom =
      (RingHom.ker (algebraMap R S)).map (algebraMap R A'))
    (f g : A) (J : Ideal A) (hJ : J = Ideal.span ({f, g} : Set A))
    (hf : f ∈ A⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (A ⧸ Ideal.span {f})⁰)
    [Module.Finite S (A ⧸ J)] [Module.Flat S (A ⧸ J)] :
    ∃ f' g' : A', π f' = f ∧ π g' = g ∧
      J = (Ideal.span ({f', g'} : Set A')).map π.toRingHom ∧
      Module.Finite R (A' ⧸ Ideal.span ({f', g'} : Set A')) ∧
      Module.Free R (A' ⧸ Ideal.span ({f', g'} : Set A')) ∧
      Module.Flat R (A' ⧸ Ideal.span ({f', g'} : Set A')) ∧
      Module.finrank R (A' ⧸ Ideal.span ({f', g'} : Set A')) = Module.finrank S (A ⧸ J) := by
  obtain ⟨f', hf'⟩ := hπ f
  obtain ⟨g', hg'⟩ := hπ g
  subst f
  subst g
  have hJ' : J = (Ideal.span ({f', g'} : Set A')).map π.toRingHom := by
    rw [liftedRegularPair_wholeIdeal_map165 π.toRingHom f' g']
    change J = Ideal.span ({π f', π g'} : Set A)
    exact hJ
  have hflat := liftedRegularPair_prescribedFiniteFlat_local166 hRS hI π hπ hK
    f' g' J hJ' hf hg
  exact ⟨f', g', rfl, rfl, hJ', hflat⟩

end AllCharacteristics
