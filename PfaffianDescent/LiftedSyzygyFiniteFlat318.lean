import PfaffianDescent.LiftedSyzygyIdealIntersection318

/-!
A finite syzygy presentation supplies the ideal-intersection calculation
for square-zero lifting. The actual-basis theorem then constructs finite
freeness and flatness of the whole lifted quotient with the prescribed
rank. Flatness of the new quotient is a conclusion.
-/

noncomputable section
namespace AllCharacteristics
open Module LinearMap TensorProduct
open scoped BigOperators
universe u v w t

/-- Arbitrary finite syzygies replace the two-generator regular-pair
assumption of166. The actual original quotient and its basis are retained. -/
theorem liftedSyzygy_prescribedFiniteFreeFlat318
    {R : Type u} {S : Type v} {A' : Type w} {A : Type t}
    [CommRing R] [Nontrivial R] [CommRing S] [CommRing A'] [CommRing A]
    [Algebra R S] [Algebra R A'] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] [Module.Flat R A']
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (hRS : Function.Surjective (algebraMap R S))
    (hI : (RingHom.ker (algebraMap R S)) ^ 2 = ⊥)
    (π : A' →ₐ[R] A) (hπ : Function.Surjective π)
    (hK : RingHom.ker π.toRingHom =
      (RingHom.ker (algebraMap R S)).map (algebraMap R A'))
    (f : ι → A') (M : ι → κ → A') (J : Ideal A)
    (hJ : J = (Ideal.span (Set.range f)).map π.toRingHom)
    (hsyz : ∀ j, ∑ i, f i * M i j = 0)
    (hrelations : ∀ a : ι → A, (∑ i, a i * π (f i)) = 0 →
      ∃ b : κ → A, ∀ i, a i = ∑ j, π (M i j) * b j)
    (d : ℕ) (b : Basis (Fin d) S (A ⧸ J)) :
    ∃ b' : Basis (Fin d) R (A' ⧸ Ideal.span (Set.range f)),
      Module.Finite R (A' ⧸ Ideal.span (Set.range f)) ∧
      Module.Free R (A' ⧸ Ideal.span (Set.range f)) ∧
      Module.Flat R (A' ⧸ Ideal.span (Set.range f)) ∧
      Module.finrank R (A' ⧸ Ideal.span (Set.range f)) = d ∧
      ∀ i, (Ideal.quotientEquivAlgOfEq S hJ.symm)
        (embeddedIdealReduction165 π (Ideal.span (Set.range f)) (b' i)) = b i := by
  let I := RingHom.ker (algebraMap R S)
  let J' := Ideal.span (Set.range f)
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
    exact liftedSyzygy_kernel_inf_eq_mul318 π.toRingHom hπ f M hsyz hrelations
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

/-- Over the actual local downstairs algebra, finite flatness constructs
the input basis. All upstairs finite/free/flat conclusions are derived. -/
theorem liftedSyzygy_prescribedFiniteFlat_local318
    {R : Type u} {S : Type v} {A' : Type w} {A : Type t}
    [CommRing R] [CommRing S] [IsLocalRing S] [CommRing A'] [CommRing A]
    [Algebra R S] [Algebra R A'] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] [Module.Flat R A']
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (hRS : Function.Surjective (algebraMap R S))
    (hI : (RingHom.ker (algebraMap R S)) ^ 2 = ⊥)
    (π : A' →ₐ[R] A) (hπ : Function.Surjective π)
    (hK : RingHom.ker π.toRingHom =
      (RingHom.ker (algebraMap R S)).map (algebraMap R A'))
    (f : ι → A') (M : ι → κ → A') (J : Ideal A)
    (hJ : J = (Ideal.span (Set.range f)).map π.toRingHom)
    (hsyz : ∀ j, ∑ i, f i * M i j = 0)
    (hrelations : ∀ a : ι → A, (∑ i, a i * π (f i)) = 0 →
      ∃ b : κ → A, ∀ i, a i = ∑ j, π (M i j) * b j)
    [Module.Finite S (A ⧸ J)] [Module.Flat S (A ⧸ J)] :
    Module.Finite R (A' ⧸ Ideal.span (Set.range f)) ∧
      Module.Free R (A' ⧸ Ideal.span (Set.range f)) ∧
      Module.Flat R (A' ⧸ Ideal.span (Set.range f)) ∧
      Module.finrank R (A' ⧸ Ideal.span (Set.range f)) = Module.finrank S (A ⧸ J) := by
  letI : Nontrivial R := (algebraMap R S).domain_nontrivial
  letI : Module.Free S (A ⧸ J) := Module.free_of_flat_of_isLocalRing
  obtain ⟨b', hfinite, hfree, hflat, hrank, hb'⟩ :=
    liftedSyzygy_prescribedFiniteFreeFlat318 hRS hI π hπ hK f M J hJ hsyz hrelations
      (Module.finrank S (A ⧸ J)) (Module.finBasis S (A ⧸ J))
  exact ⟨hfinite, hfree, hflat, hrank⟩

end AllCharacteristics
end
